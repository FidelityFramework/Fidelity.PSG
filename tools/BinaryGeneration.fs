// Generate the complete closed-world snapshot mapping. Reflection is a build-time
// tool only; the emitted codec contains typed field access and constructors.
// Usage: dotnet fsi tools/GenerateBinary.fsx <Fidelity.PSG.dll> <output.fs>
module PsgBinaryGeneration

open System
open System.Reflection
open Microsoft.FSharp.Reflection

let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private generic (ty: Type) = if ty.IsGenericType then ty.GetGenericTypeDefinition().FullName else ""
let private isKind (prefix: string) ty = (generic ty).StartsWith(prefix, StringComparison.Ordinal)
let private isList = isKind "Microsoft.FSharp.Collections.FSharpList`"
let private isMap = isKind "Microsoft.FSharp.Collections.FSharpMap`"
let private isSet = isKind "Microsoft.FSharp.Collections.FSharpSet`"
let private isOption = isKind "Microsoft.FSharp.Core.FSharpOption`"
let private isResult = isKind "Microsoft.FSharp.Core.FSharpResult`"
let private primitive (ty: Type) =
    match ty.FullName with
    | "System.Boolean" -> Some "Bool"
    | "System.Byte" -> Some "U8"
    | "System.Char" -> Some "Char"
    | "System.Decimal" -> Some "Decimal"
    | "System.Double" -> Some "F64"
    | "System.Int32" -> Some "I32"
    | "System.Int64" -> Some "I64"
    | "System.UInt16" -> Some "U16"
    | "System.UInt64" -> Some "U64"
    | "System.Numerics.BigInteger" -> Some "BigInteger"
    | "System.String" -> Some "String"
    | _ -> None
let private named (ty: Type) =
    (ty.Namespace = "Fidelity.PSG" || ty.Namespace = "BAREWire.Platform") &&
    not ty.IsArray && not ty.IsGenericType &&
    (FSharpType.IsRecord(ty, flags) || FSharpType.IsUnion(ty, flags))
let private children (ty: Type) =
    if ty.IsArray && ty.GetArrayRank() = 1 then [|ty.GetElementType()|]
    elif FSharpType.IsTuple ty then FSharpType.GetTupleElements ty
    elif isList ty || isMap ty || isSet ty || isOption ty || isResult ty then ty.GetGenericArguments()
    elif named ty && FSharpType.IsRecord(ty, flags) then FSharpType.GetRecordFields(ty, flags) |> Array.map _.PropertyType
    elif named ty && FSharpType.IsUnion(ty, flags) then FSharpType.GetUnionCases(ty, flags) |> Array.collect (fun c -> c.GetFields() |> Array.map _.PropertyType)
    elif primitive ty |> Option.isSome then [||]
    else failwithf "No complete binary mapping declared for %s" ty.FullName
let private sourceName (ty: Type) =
    if ty.IsNested then
        let owner = ty.DeclaringType
        let ownerName = if owner.Name.EndsWith "Module" then owner.Name.Substring(0, owner.Name.Length - 6) else owner.Name
        "global." + owner.Namespace + "." + ownerName + "." + ty.Name
    else "global." + ty.FullName
let private identifier (ty: Type) = ty.FullName.Replace('.', '_').Replace('+', '_')
let private quoted value = "``" + value + "``"
let private caseName ty name = sourceName ty + (if name = ty.Name then "" else "." + quoted name)

let generate (assemblyPath: string) =
    let contract = Assembly.LoadFrom(IO.Path.GetFullPath assemblyPath)
    let revision = contract.GetType("Fidelity.PSG.Revision", throwOnError = true)
    let rec visit seen ty =
        if List.contains ty seen then seen
        else children ty |> Array.fold visit (ty :: seen)
    let all = visit [] revision |> List.toArray
    let types = all |> Array.filter named |> Array.sortBy _.FullName
    let schemaField =
        contract.GetTypes()
        |> Array.collect (fun ty -> ty.GetFields(BindingFlags.Public ||| BindingFlags.Static))
        |> Array.find (fun field -> field.Name = "Schema" && field.DeclaringType.Name.StartsWith "Revision")
    let schema = schemaField.GetRawConstantValue() :?> int

    let rec shape (ty: Type) =
        if ty.IsArray then "array<" + shape (ty.GetElementType()) + ">"
        elif FSharpType.IsTuple ty then (if ty.IsValueType then "structtuple<" else "tuple<") + (FSharpType.GetTupleElements ty |> Array.map shape |> String.concat ",") + ">"
        elif ty.IsGenericType then generic ty + "<" + (ty.GetGenericArguments() |> Array.map shape |> String.concat ",") + ">"
        else ty.FullName
    let descriptions =
        types |> Array.map (fun ty ->
            let fields (fields: PropertyInfo array) = fields |> Array.map(fun field -> field.Name + ":" + shape field.PropertyType) |> String.concat ";"
            if FSharpType.IsRecord(ty, flags) then ty.FullName + "=record{" + fields (FSharpType.GetRecordFields(ty, flags)) + "}"
            else
                ty.FullName + "=union{" +
                (FSharpType.GetUnionCases(ty, flags) |> Array.sortBy _.Tag |> Array.map(fun case -> string case.Tag + ":" + case.Name + "(" + fields (case.GetFields()) + ")") |> String.concat ";") + "}")
    let manifest = "Fidelity.PSG.Binary/1\nSchema=" + string schema + "\n" + String.concat "\n" descriptions + "\n"
    let fingerprint = System.Security.Cryptography.SHA256.HashData(Text.Encoding.UTF8.GetBytes manifest) |> Convert.ToHexString

    let rec writer depth ty =
        match primitive ty with
        | Some name -> "write" + name
        | None when named ty -> "write_" + identifier ty
        | None when ty.IsArray -> "(writeArray " + writer (depth + 1) (ty.GetElementType()) + ")"
        | None when isList ty || isSet ty || isOption ty ->
            let combinator = if isList ty then "writeList" elif isSet ty then "writeSet" else "writeOption"
            "(" + combinator + " " + writer (depth + 1) (ty.GetGenericArguments()[0]) + ")"
        | None when isMap ty || isResult ty ->
            let args = ty.GetGenericArguments()
            "(" + (if isMap ty then "writeMap" else "writeResult") + " " + writer (depth + 1) args[0] + " " + writer (depth + 1) args[1] + ")"
        | None when FSharpType.IsTuple ty ->
            let elements = FSharpType.GetTupleElements ty
            let names = elements |> Array.mapi(fun i _ -> sprintf "v%d_%d" depth i)
            let pattern = (if ty.IsValueType then "struct " else "") + "(" + String.concat ", " names + ")"
            let body =
                Array.zip elements names |> Array.foldBack (fun (ty, name) rest ->
                    writer (depth + 1) ty + " state " + name + " |> Result.bind (fun state -> " + rest + ")") <| "Ok(leaveWrite state)"
            "(fun state " + pattern + " -> enterWrite state |> Result.bind (fun state -> " + body + "))"
        | _ -> failwithf "Unsupported writer: %s" ty.FullName
    let rec reader depth ty =
        match primitive ty with
        | Some name -> "read" + name
        | None when named ty -> "read_" + identifier ty
        | None when ty.IsArray -> "(readArray " + reader (depth + 1) (ty.GetElementType()) + ")"
        | None when isList ty || isSet ty || isOption ty ->
            let combinator = if isList ty then "readList" elif isSet ty then "readSet" else "readOption"
            "(" + combinator + " " + reader (depth + 1) (ty.GetGenericArguments()[0]) + ")"
        | None when isMap ty || isResult ty ->
            let args = ty.GetGenericArguments()
            "(" + (if isMap ty then "readMap" else "readResult") + " " + reader (depth + 1) args[0] + " " + reader (depth + 1) args[1] + ")"
        | None when FSharpType.IsTuple ty ->
            let elements = FSharpType.GetTupleElements ty
            let names = elements |> Array.mapi(fun i _ -> sprintf "v%d_%d" depth i)
            let value = (if ty.IsValueType then "struct " else "") + "(" + String.concat ", " names + ")"
            let body =
                Array.zip elements names |> Array.foldBack (fun (ty, name) rest ->
                    reader (depth + 1) ty + " state |> Result.bind (fun (" + name + ", state) -> " + rest + ")") <| ("Ok(" + value + ", leaveRead state)")
            "(fun state -> enterRead state |> Result.bind (fun state -> " + body + "))"
        | _ -> failwithf "Unsupported reader: %s" ty.FullName

    let writeDefinition first ty =
        let prefix = if first then "let rec" else "and"
        let header = "    " + prefix + " write_" + identifier ty + " (state: WriteState) (value: " + sourceName ty + ") : Result<WriteState, BinaryError> = result {\n        let! state = enterWrite state\n"
        let writeFields indent (fields: PropertyInfo array) values =
            Array.map2(fun (field: PropertyInfo) value -> indent + "let! state = " + writer 0 field.PropertyType + " state " + value + "\n") fields values |> String.concat ""
        if FSharpType.IsRecord(ty, flags) then
            let fields = FSharpType.GetRecordFields(ty, flags)
            header + writeFields "        " fields (fields |> Array.map(fun field -> "value." + quoted field.Name)) + "        return leaveWrite state\n    }\n"
        else
            let cases = FSharpType.GetUnionCases(ty, flags) |> Array.sortBy _.Tag |> Array.map(fun case ->
                let fields = case.GetFields()
                let names = fields |> Array.mapi(fun i _ -> "a" + string i)
                let pattern = caseName ty case.Name + (if fields.Length = 0 then "" else "(" + String.concat ", " names + ")")
                "            | " + pattern + " -> result {\n                let! state = writeTag state " + string case.Tag + "\n" +
                writeFields "                " fields names + "                return leaveWrite state\n              }\n")
            header + "        return!\n            match value with\n" + String.concat "" cases + "    }\n"
    let readDefinition first ty =
        let prefix = if first then "let rec" else "and"
        let header = "    " + prefix + " read_" + identifier ty + " (state: ReadState) : Result<" + sourceName ty + " * ReadState, BinaryError> = result {\n        let! state = enterRead state\n"
        let readFields indent (fields: PropertyInfo array) =
            fields |> Array.mapi(fun i field -> indent + "let! a" + string i + ", state = " + reader 0 field.PropertyType + " state\n") |> String.concat ""
        if FSharpType.IsRecord(ty, flags) then
            let fields = FSharpType.GetRecordFields(ty, flags)
            let values = fields |> Array.mapi(fun i field -> quoted field.Name + " = a" + string i) |> String.concat "; "
            header + readFields "        " fields + "        return ({ " + values + " } : " + sourceName ty + "), leaveRead state\n    }\n"
        else
            let cases = FSharpType.GetUnionCases(ty, flags) |> Array.sortBy _.Tag |> Array.map(fun case ->
                let fields = case.GetFields()
                let values = fields |> Array.mapi(fun i _ -> "a" + string i)
                let value = caseName ty case.Name + (if fields.Length = 0 then "" else "(" + String.concat ", " values + ")")
                "            | " + string case.Tag + " -> result {\n" + readFields "                " fields + "                return " + value + ", leaveRead state\n              }\n")
            header + "        let! tag, state = readTag state\n        return!\n            match tag with\n" + String.concat "" cases +
            "            | _ -> malformed state \"Unknown " + ty.FullName + " case\"\n    }\n"
    String.concat "\n" [
        "// Generated by tools/GenerateBinary.fsx. Every reachable record field and union case is explicit."
        "namespace Fidelity.PSG"
        "module internal BinaryGenerated ="
        "    open BinaryRuntime"
        "    [<Literal>]"
        "    let Format = 1u"
        "    [<Literal>]"
        "    let Schema = " + string schema
        "    [<Literal>]"
        "    let Fingerprint = \"" + fingerprint + "\""
        "    [<Literal>]"
        "    let NamedTypes = " + string types.Length
        types |> Array.mapi(fun i ty -> writeDefinition (i = 0) ty) |> String.concat "\n"
        types |> Array.mapi(fun i ty -> readDefinition (i = 0) ty) |> String.concat "\n"
        "    let writeRevision = write_" + identifier revision
        "    let readRevision = read_" + identifier revision
        "" ]
