// Generates src/Fidelity.PSG/IntegrityNamed.fs from the compiled contract.
//
// The generated module lists every position of a revision that holds a node
// identity. The structural rule "every identity named is a node held" is then
// complete by construction: a table added to the contract is covered when this
// script runs again, and the build gate compares the generated file with the
// contract it was generated from.
//
// Usage: dotnet fsi tools/GenerateIntegrity.fsx <Fidelity.PSG.dll> <output file>

open System
open System.Reflection
open Microsoft.FSharp.Reflection

let arguments = fsi.CommandLineArgs |> Array.skip 1
if arguments.Length <> 2 then
    eprintfn "Usage: dotnet fsi tools/GenerateIntegrity.fsx <Fidelity.PSG.dll> <output file>"
    exit 2

let contract = Assembly.LoadFrom(IO.Path.GetFullPath arguments[0])
let flags = BindingFlags.Public ||| BindingFlags.NonPublic

let named (name: string) =
    contract.GetTypes() |> Array.find (fun ty -> ty.Namespace = "Fidelity.PSG" && ty.Name = name)

let nodeId = named "NodeId"
let revision = named "Revision"

let isRecord (ty: Type) = FSharpType.IsRecord(ty, flags)
let isUnion (ty: Type) = FSharpType.IsUnion(ty, flags)
let generic (ty: Type) = if ty.IsGenericType then ty.GetGenericTypeDefinition().FullName else ""
let isList ty = (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpList"
let isSet ty = (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpSet"
let isMap ty = (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpMap"
let isOption ty = (generic ty).StartsWith "Microsoft.FSharp.Core.FSharpOption"
let isResult ty = (generic ty).StartsWith "Microsoft.FSharp.Core.FSharpResult"
let isTuple (ty: Type) = FSharpType.IsTuple ty
let isContract (ty: Type) = ty.Assembly = contract && (isRecord ty || isUnion ty) && not (isList ty || isOption ty)

/// Whether a value of the type can hold a node identity, at any depth.
let holds : Type -> bool =
    let known = Collections.Generic.Dictionary<Type, bool>()
    let rec visit (pending: Set<string>) (ty: Type) : bool =
        if ty = nodeId then true
        elif known.ContainsKey ty then known[ty]
        elif pending.Contains ty.FullName then false
        else
            let inner = pending.Add ty.FullName
            let answer =
                if isList ty || isSet ty || isMap ty || isOption ty || isResult ty then
                    ty.GetGenericArguments() |> Array.exists (visit inner)
                elif isTuple ty then FSharpType.GetTupleElements ty |> Array.exists (visit inner)
                elif ty.Assembly = contract && isRecord ty then
                    FSharpType.GetRecordFields(ty, flags) |> Array.exists (fun field -> visit inner field.PropertyType)
                elif ty.Assembly = contract && isUnion ty then
                    FSharpType.GetUnionCases(ty, flags)
                    |> Array.exists (fun case -> case.GetFields() |> Array.exists (fun field -> visit inner field.PropertyType))
                else false
            if pending.IsEmpty then known[ty] <- answer
            answer
    visit Set.empty

/// The source name of a contract type, qualified where it is nested in a module.
let rec sourceName (ty: Type) : string =
    if ty.IsNested && not (isNull ty.DeclaringType) then
        let owner = ty.DeclaringType
        let ownerName = if owner.Name.EndsWith "Module" then owner.Name.Substring(0, owner.Name.Length - 6) else owner.Name
        "Fidelity.PSG." + ownerName + "." + ty.Name
    else "Fidelity.PSG." + ty.Name

let functionName (ty: Type) = "idsOf" + ty.Name

/// An expression of type NodeId list that collects the identities of `value`.
let rec collect (depth: int) (ty: Type) (value: string) : string =
    let bound = sprintf "v%d" depth
    if not (holds ty) then "[]"
    elif ty = nodeId then sprintf "[ %s ]" value
    elif isList ty then
        sprintf "(%s |> List.collect (fun %s -> %s))" value bound (collect (depth + 1) (ty.GetGenericArguments()[0]) bound)
    elif isSet ty then
        sprintf "(%s |> Set.toList |> List.collect (fun %s -> %s))" value bound (collect (depth + 1) (ty.GetGenericArguments()[0]) bound)
    elif isOption ty then
        sprintf "(%s |> Option.toList |> List.collect (fun %s -> %s))" value bound (collect (depth + 1) (ty.GetGenericArguments()[0]) bound)
    elif isMap ty then
        let arguments = ty.GetGenericArguments()
        let key, held = sprintf "k%d" depth, sprintf "h%d" depth
        sprintf "(%s |> Map.toList |> List.collect (fun (%s, %s) -> %s @ %s))" value key held
            (collect (depth + 1) arguments[0] key) (collect (depth + 1) arguments[1] held)
    elif isResult ty then
        let arguments = ty.GetGenericArguments()
        sprintf "(match %s with Ok %s -> %s | Error %s -> %s)" value bound (collect (depth + 1) arguments[0] bound) bound (collect (depth + 1) arguments[1] bound)
    elif isTuple ty then
        let elements = FSharpType.GetTupleElements ty
        let names = elements |> Array.mapi (fun index _ -> sprintf "t%d_%d" depth index)
        let parts = Array.map2 (fun element name -> collect (depth + 1) element name) elements names |> Array.filter ((<>) "[]")
        sprintf "(let (%s) = %s in %s)" (String.concat ", " names) value (if parts.Length = 0 then "[]" else String.concat " @ " parts)
    elif isContract ty then sprintf "(%s %s)" (functionName ty) value
    else "[]"

/// Every contract record and union that can hold an identity, reached from the revision.
let reached : Type list =
    let rec visit (seen: Type list) (ty: Type) : Type list =
        if not (holds ty) || ty = nodeId then seen
        elif isList ty || isSet ty || isMap ty || isOption ty || isResult ty then
            ty.GetGenericArguments() |> Array.fold visit seen
        elif isTuple ty then FSharpType.GetTupleElements ty |> Array.fold visit seen
        elif isContract ty then
            if List.contains ty seen then seen
            else
                let seen = ty :: seen
                if isRecord ty then
                    FSharpType.GetRecordFields(ty, flags) |> Array.fold (fun seen field -> visit seen field.PropertyType) seen
                else
                    FSharpType.GetUnionCases(ty, flags)
                    |> Array.fold (fun seen case -> case.GetFields() |> Array.fold (fun seen field -> visit seen field.PropertyType) seen) seen
        else seen
    visit [] revision |> List.filter (fun ty -> ty <> revision) |> List.sortBy (fun ty -> ty.Name)

let definition (first: bool) (ty: Type) : string =
    let keyword = if first then "let rec private" else "and private"
    let head = sprintf "    %s %s (value: %s) : NodeId list =" keyword (functionName ty) (sourceName ty)
    if isRecord ty then
        let parts =
            FSharpType.GetRecordFields(ty, flags)
            |> Array.map (fun field -> collect 0 field.PropertyType ("value." + field.Name))
            |> Array.filter ((<>) "[]")
        let body = if parts.Length = 0 then "[]" else String.concat "\n        @ " parts
        head + "\n        " + body
    else
        let cases =
            FSharpType.GetUnionCases(ty, flags)
            |> Array.map (fun case ->
                let fields = case.GetFields()
                let names = fields |> Array.mapi (fun index _ -> sprintf "a%d" index)
                let parts = Array.map2 (fun (field: PropertyInfo) name -> collect 0 field.PropertyType name) fields names |> Array.filter ((<>) "[]")
                let used = Array.map2 (fun (field: PropertyInfo) name -> if collect 0 field.PropertyType name = "[]" then "_" else name) fields names
                let pattern =
                    if fields.Length = 0 then sprintf "%s.%s" (sourceName ty) case.Name
                    else sprintf "%s.%s(%s)" (sourceName ty) case.Name (String.concat ", " used)
                sprintf "        | %s -> %s" pattern (if parts.Length = 0 then "[]" else String.concat " @ " parts))
        head + "\n        match value with\n" + String.concat "\n" cases

/// The parts of the revision: one for each table, and one for each field of a
/// table's rows where the rows are records.
let rec parts (path: string) (value: string) (ty: Type) : (string * string) list =
    if not (holds ty) then []
    elif ty.Assembly = contract && isRecord ty && ty <> nodeId then
        FSharpType.GetRecordFields(ty, flags)
        |> Array.toList
        |> List.collect (fun field ->
            parts (if path = "" then field.Name else path + "." + field.Name) (value + "." + field.Name) field.PropertyType)
    else
        let rows (row: Type) (each: string -> string) : (string * string) list =
            if row.Assembly = contract && isRecord row then
                FSharpType.GetRecordFields(row, flags)
                |> Array.toList
                |> List.filter (fun field -> holds field.PropertyType)
                |> List.map (fun field -> path + "." + field.Name, each (collect 1 field.PropertyType ("row." + field.Name)))
            elif holds row then [ path + " (values)", each (collect 1 row "row") ]
            else []
        if isMap ty then
            let arguments = ty.GetGenericArguments()
            let keys =
                if holds arguments[0] then
                    [ path, sprintf "(%s |> Map.toList |> List.collect (fun (key, _) -> %s))" value (collect 1 arguments[0] "key") ]
                else []
            keys @ rows arguments[1] (fun body -> sprintf "(%s |> Map.toList |> List.collect (fun (_, row) -> %s))" value body)
        elif isList ty then
            rows (ty.GetGenericArguments()[0]) (fun body -> sprintf "(%s |> List.collect (fun row -> %s))" value body)
            |> List.map (fun (part, body) -> (if part.EndsWith " (values)" then path else part), body)
        elif isOption ty && (let inner = ty.GetGenericArguments()[0] in inner.Assembly = contract && isRecord inner) then
            rows (ty.GetGenericArguments()[0]) (fun body -> sprintf "(%s |> Option.toList |> List.collect (fun row -> %s))" value body)
        else [ path, collect 0 ty value ]

let entries = parts "" "revision" revision

let text =
    [ "// Generated by tools/GenerateIntegrity.fsx from the compiled contract. Do not edit."
      "// Run the generator again after any change to the contract types."
      "namespace Fidelity.PSG"
      ""
      "/// Every position of a revision that holds a node identity."
      "[<RequireQualifiedAccess>]"
      "module IntegrityNamed ="
      ""
      reached |> List.mapi (fun index ty -> definition (index = 0) ty) |> String.concat "\n\n"
      ""
      "    /// Every stored node identity, including the body's own identity and context handles."
      "    let nodeReferences (node: SemanticNode) : NodeId list = idsOfSemanticNode node"
      ""
      "    /// Every stored identity in a declaration context header and its sparse ports."
      "    let contextHeaderReferences (header: SourceContextHeader) : NodeId list = idsOfSourceContextHeader header"
      ""
      // The parts are listed in groups. One list of every part is more than the
      // compiler accepts as a single expression.
      entries
      |> List.chunkBySize 24
      |> List.mapi (fun index group ->
          sprintf "    let private group%d (revision: Revision) : (string * NodeId list) list =\n        [ " index
          + (group |> List.map (fun (part, body) -> sprintf "\"%s\", %s" part body) |> String.concat "\n          ")
          + " ]")
      |> String.concat "\n\n"
      ""
      "    /// Every part of a revision that names nodes, with the identities it names."
      "    let named (revision: Revision) : (string * NodeId list) list ="
      "        List.concat\n            [ " + (entries |> List.chunkBySize 24 |> List.mapi (fun index _ -> sprintf "group%d revision" index) |> String.concat "\n              ") + " ]"
      ""
      sprintf "    /// The number of parts listed. The build compares it with the contract."
      sprintf "    [<Literal>]"
      sprintf "    let Parts = %d" entries.Length
      "" ]
    |> String.concat "\n"

IO.File.WriteAllText(IO.Path.GetFullPath arguments[1], text)
printfn "%d parts, %d functions, %d lines" entries.Length reached.Length (text.Split('\n').Length)
