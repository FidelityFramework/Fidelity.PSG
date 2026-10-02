// Reflection is restricted to this generation tool and coverage tests.
module PsgJsonGeneration

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
    | "System.Byte" -> Some "Byte"
    | "System.Char" -> Some "Char"
    | "System.Decimal" -> Some "Decimal"
    | "System.Double" -> Some "Double"
    | "System.Int32" -> Some "Int32"
    | "System.Int64" -> Some "Int64"
    | "System.UInt16" -> Some "UInt16"
    | "System.UInt64" -> Some "UInt64"
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
    else failwithf "No complete JSON inspection mapping declared for %s" ty.FullName
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
    let types = visit [] revision |> List.filter named |> List.sortBy _.FullName |> List.toArray
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
            let values = Array.map2(fun item name -> writer (depth + 1) item + " " + name) elements names
            "(fun " + pattern + " -> JsonValue.Array [" + String.concat "; " values + "])"
        | _ -> failwithf "Unsupported inspection writer: %s" ty.FullName
    let definition first ty =
        let header = "    " + (if first then "let rec" else "and") + " write_" + identifier ty + " (value: " + sourceName ty + ") : JsonValue =\n"
        let fields (fields: PropertyInfo array) values =
            Array.map2(fun (field: PropertyInfo) value -> sprintf "(%A, %s %s)" field.Name (writer 0 field.PropertyType) value) fields values |> String.concat "; "
        if FSharpType.IsRecord(ty, flags) then
            let properties = FSharpType.GetRecordFields(ty, flags)
            header + "        JsonValue.Object [" + fields properties (properties |> Array.map(fun field -> "value." + quoted field.Name)) + "]\n"
        else
            let cases = FSharpType.GetUnionCases(ty, flags) |> Array.sortBy _.Tag |> Array.map(fun case ->
                let properties = case.GetFields()
                let names = properties |> Array.mapi(fun i _ -> "a" + string i)
                let pattern = caseName ty case.Name + (if properties.Length = 0 then "" else "(" + String.concat ", " names + ")")
                "        | " + pattern + " -> union " + sprintf "%A" case.Name + " [" + fields properties names + "]")
            header + "        match value with\n" + String.concat "\n" cases + "\n"
    String.concat "\n" [
        "// Generated by tools/GenerateJson.fsx. Every reachable field and union case is explicit."
        "namespace Fidelity.PSG.Json"
        "open Fidelity.Data.JSON"
        "module internal JsonGenerated ="
        "    open JsonRuntime"
        "    [<Literal>]"
        "    let NamedTypes = " + string types.Length
        types |> Array.mapi(fun i ty -> definition (i = 0) ty) |> String.concat "\n"
        "    let writeRevision = write_" + identifier revision
        "" ]
