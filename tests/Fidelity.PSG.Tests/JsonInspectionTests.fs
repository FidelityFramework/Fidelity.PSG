module Fidelity.PSG.Tests.JsonInspectionTests

open System
open System.IO
open System.Collections
open System.Reflection
open System.Globalization
open Microsoft.FSharp.Reflection
open Xunit
open Fidelity.PSG
open Fidelity.PSG.Json
open Fidelity.Data.JSON

let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private generic (ty: Type) = if ty.IsGenericType then ty.GetGenericTypeDefinition().FullName else ""

// Reflection belongs only in the generator and this independent coverage test.
// Production readers/writers use statically generated field access and DU cases.
type private Containers =
    static member Set<'a when 'a: comparison>(values: obj array) = values |> Array.map unbox<'a> |> Set.ofArray |> box
    static member Map<'a, 'b when 'a: comparison>(key: obj, value: obj) = Map.ofList [unbox<'a> key, unbox<'b> value] |> box
    static member EmptyMap<'a, 'b when 'a: comparison>() = Map.empty<'a, 'b> |> box

let private container name arguments values =
    let methodInfo = typeof<Containers>.GetMethod(name, BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static)
    if isNull methodInfo then failwithf "Test container constructor %s was not found" name
    methodInfo.MakeGenericMethod(arguments).Invoke(null, values)

let rec private sample depth seed (ty: Type) : obj =
    if depth > 32 then failwithf "No finite test value for %s" ty.FullName
    match ty.FullName with
    | "System.Boolean" -> box (seed % 2 = 0)
    | "System.Byte" -> box (byte (seed % 251))
    | "System.Char" -> box (char (0x400 + seed % 200))
    | "System.Decimal" -> box (Decimal(seed, 0, 0, seed % 2 = 0, 3uy))
    | "System.Double" -> box (float seed / 8.0)
    | "System.Int32" -> box (seed * 17 - 1000)
    | "System.Int64" -> box (int64 seed * 100000003L)
    | "System.UInt16" -> box (uint16 (seed % 65536))
    | "System.UInt64" -> box (UInt64.MaxValue - uint64 seed)
    | "System.Numerics.BigInteger" -> box ((bigint.One <<< 190) + bigint seed)
    | "System.String" -> box (sprintf "field-%d-λ" seed)
    | _ when ty.IsArray ->
        let itemType = ty.GetElementType()
        let values = Array.CreateInstance(itemType, if depth < 3 then 1 else 0)
        if values.Length <> 0 then values.SetValue(sample (depth + 1) (seed + 1) itemType, 0)
        box values
    | _ when FSharpType.IsTuple ty ->
        FSharpType.GetTupleElements ty
        |> Array.mapi(fun at field -> sample (depth + 1) (seed * 3 + at + 1) field)
        |> fun values -> FSharpValue.MakeTuple(values, ty)
    | _ when (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpMap`" ->
        let args = ty.GetGenericArguments()
        if depth < 3 then container "Map" args [|sample (depth + 1) (seed + 1) args[0]; sample (depth + 1) (seed + 2) args[1]|]
        else container "EmptyMap" args [||]
    | _ when (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpSet`" ->
        let args = ty.GetGenericArguments()
        let values = if depth < 3 then [|sample (depth + 1) (seed + 1) args[0]|] else [||]
        container "Set" args [|box values|]
    | _ when (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpList`" ->
        let cases = FSharpType.GetUnionCases(ty, flags)
        let empty = FSharpValue.MakeUnion(cases |> Array.find(fun case -> case.GetFields().Length = 0), [||], flags)
        if depth >= 3 then empty
        else
            let cons = cases |> Array.find(fun case -> case.GetFields().Length = 2)
            FSharpValue.MakeUnion(cons, [|sample (depth + 1) (seed + 1) (ty.GetGenericArguments()[0]); empty|], flags)
    | _ when FSharpType.IsRecord(ty, flags) ->
        FSharpType.GetRecordFields(ty, flags)
        |> Array.mapi(fun at field -> sample (depth + 1) (seed * 3 + at + 1) field.PropertyType)
        |> fun values -> FSharpValue.MakeRecord(ty, values, flags)
    | _ when FSharpType.IsUnion(ty, flags) ->
        let cases = FSharpType.GetUnionCases(ty, flags)
        let chosen = cases |> Array.minBy(fun case -> case.GetFields().Length, case.Tag)
        let fields = chosen.GetFields() |> Array.mapi(fun at field -> sample (depth + 1) (seed * 3 + at + 1) field.PropertyType)
        FSharpValue.MakeUnion(chosen, fields, flags)
    | _ -> failwithf "Test census cannot construct %s" ty.FullName

let private take = function Ok value -> value | Error error -> failwithf "%A" error
let private properties = function
    | JsonValue.Object pairs ->
        Assert.Equal(pairs.Length, (Map.ofList pairs).Count)
        Map.ofList pairs
    | other -> failwithf "Expected object: %A" other
let private items = function JsonValue.Array values -> values | other -> failwithf "Expected array: %A" other
let private text = function JsonValue.String value -> value | other -> failwithf "Expected exact text: %A" other
let private number json =
    match JsonValue.tryAsInt64 json with
    | Some value -> value
    | None -> failwithf "Expected bounded integer literal: %A" json

// Independent reflection examines the original value, including every declared
// field and constructor. No reflection ships with the inspection assembly.
let rec private check (ty: Type) (value: obj) json =
    let typed kind =
        let fields = properties json
        Assert.Equal(kind, fields["$type"] |> text)
        fields
    match ty.FullName with
    | "System.Boolean" -> Assert.Equal(JsonValue.Bool(unbox value), json)
    | "System.String" -> Assert.Equal(unbox<string> value, text json)
    | "System.Byte" | "System.UInt16" | "System.Int32" -> Assert.Equal(Convert.ToInt64(value, CultureInfo.InvariantCulture), number json)
    | "System.Int64" -> Assert.Equal((unbox<int64> value).ToString(CultureInfo.InvariantCulture), (typed "int64")["value"] |> text)
    | "System.UInt64" -> Assert.Equal((unbox<uint64> value).ToString(CultureInfo.InvariantCulture), (typed "uint64")["value"] |> text)
    | "System.Numerics.BigInteger" -> Assert.Equal((unbox<bigint> value).ToString(CultureInfo.InvariantCulture), (typed "bigint")["value"] |> text)
    | "System.Char" -> Assert.Equal(int64 (uint16 (unbox<char> value)), (typed "char-utf16")["codeUnit"] |> number)
    | "System.Double" ->
        let original = unbox<float> value
        let fields = typed "float64"
        Assert.Equal(sprintf "%016X" (BitConverter.DoubleToInt64Bits original), fields["bits"] |> text)
        Assert.Equal(original.ToString("R", CultureInfo.InvariantCulture), fields["value"] |> text)
    | "System.Decimal" ->
        let fields = typed "decimal"
        Assert.Equal<int>(Decimal.GetBits(unbox value), fields["bits"] |> items |> List.map(number >> int) |> List.toArray)
        Assert.Equal((unbox<decimal> value).ToString(CultureInfo.InvariantCulture), fields["value"] |> text)
    | _ when FSharpType.IsTuple ty ->
        Array.iteri (fun i field -> check field (FSharpValue.GetTupleFields value).[i] (items json).[i]) (FSharpType.GetTupleElements ty)
        Assert.Equal(FSharpType.GetTupleElements(ty).Length, (items json).Length)
    | _ when ty.IsArray || (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpSet`" || (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpList`" ->
        let element = if ty.IsArray then ty.GetElementType() else ty.GetGenericArguments()[0]
        let values = (value :?> IEnumerable) |> Seq.cast<obj> |> Seq.toList
        Assert.Equal(values.Length, (items json).Length)
        List.iter2 (check element) values (items json)
    | _ when (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpMap`" ->
        let values = (value :?> IEnumerable) |> Seq.cast<obj> |> Seq.toList
        Assert.Equal(values.Length, (items json).Length)
        List.iter2 (fun entry rendered ->
            let fields = properties rendered
            Assert.Equal<string list>(["Key"; "Value"], fields |> Map.keys |> Seq.toList)
            for i, name in [0, "Key"; 1, "Value"] do
                check (ty.GetGenericArguments()[i]) (entry.GetType().GetProperty(name).GetValue entry) fields[name]) values (items json)
    | _ when FSharpType.IsRecord(ty, flags) ->
        let fields = FSharpType.GetRecordFields(ty, flags)
        let rendered = properties json
        Assert.Equal<Set<string>>(fields |> Array.map _.Name |> Set.ofArray, rendered |> Map.keys |> Set.ofSeq)
        for field in fields do check field.PropertyType (field.GetValue value) rendered[field.Name]
    | _ when FSharpType.IsUnion(ty, flags) ->
        let case, values = FSharpValue.GetUnionFields(value, ty, flags)
        let rendered = properties json
        Assert.Equal<string list>(["$case"; "$fields"], rendered |> Map.keys |> Seq.toList)
        Assert.Equal(case.Name, rendered["$case"] |> text)
        let fields = properties rendered["$fields"]
        Assert.Equal<Set<string>>(case.GetFields() |> Array.map _.Name |> Set.ofArray, fields |> Map.keys |> Set.ofSeq)
        Array.iter2 (fun (field: PropertyInfo) item -> check field.PropertyType item fields[field.Name]) (case.GetFields()) values
    | _ -> failwithf "Missing independent inspection comparison for %s" ty.FullName

let private generated () =
    AppDomain.CurrentDomain.GetAssemblies()
    |> Array.filter(fun assembly -> assembly.IsDynamic || assembly.GetName().Name = "Fidelity.PSG.Json")
    |> Array.collect _.GetTypes()
    |> Array.tryFind(fun ty -> ty.FullName.EndsWith(".Fidelity.PSG.Json.JsonGenerated", StringComparison.Ordinal) || ty.FullName = "Fidelity.PSG.Json.JsonGenerated")
    |> Option.defaultWith(fun () -> Assembly.Load("Fidelity.PSG.Json").GetType("Fidelity.PSG.Json.JsonGenerated", true))

let private renderValue (ty: Type) value =
    let name = "write_" + ty.FullName.Replace('.', '_').Replace('+', '_')
    let methodInfo = (generated ()).GetMethod(name, BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static)
    Assert.NotNull methodInfo
    methodInfo.Invoke(null, [|value|]) :?> JsonValue

[<Fact>]
let ``inspection generator agrees with the compiled complete contract`` () =
    let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "..", ".."))
    let actual = File.ReadAllText(Path.Combine(root, "src", "Fidelity.PSG.Json", "JsonGenerated.fs"))
    Assert.Equal(PsgJsonGeneration.generate typeof<Revision>.Assembly.Location, actual)

[<Fact>]
let ``every reachable inspection field and union constructor is retained`` () =
    let rec collect seen (ty: Type) =
        if Map.containsKey ty.FullName seen then seen
        else
            let fields =
                if ty.IsArray then [|ty.GetElementType()|]
                elif FSharpType.IsTuple ty then FSharpType.GetTupleElements ty
                elif ty.IsGenericType then ty.GetGenericArguments()
                elif FSharpType.IsRecord(ty, flags) then FSharpType.GetRecordFields(ty, flags) |> Array.map _.PropertyType
                elif FSharpType.IsUnion(ty, flags) then FSharpType.GetUnionCases(ty, flags) |> Array.collect(fun c -> c.GetFields() |> Array.map _.PropertyType)
                else [||]
            Array.fold collect (Map.add ty.FullName ty seen) fields
    let types = collect Map.empty typeof<Revision> |> Map.values |> Seq.filter(fun ty -> not ty.IsGenericType && not ty.IsArray && (FSharpType.IsRecord(ty, flags) || FSharpType.IsUnion(ty, flags))) |> Seq.toArray
    let writers = (generated ()).GetMethods(BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static) |> Array.filter(fun methodInfo -> methodInfo.Name.StartsWith "write_")
    Assert.Equal(types.Length, writers.Length)
    Assert.Equal<Set<string>>(types |> Array.map _.FullName |> Set.ofArray, writers |> Array.map(fun w -> (w.GetParameters()).[0].ParameterType.FullName) |> Set.ofArray)
    let mutable casesExamined = 0
    for ty in types do
        let values =
            if FSharpType.IsUnion(ty, flags) then
                FSharpType.GetUnionCases(ty, flags) |> Array.map(fun case ->
                    let fields = case.GetFields() |> Array.mapi(fun at field -> sample 0 (at + case.Tag + 1) field.PropertyType)
                    FSharpValue.MakeUnion(case, fields, flags))
            else [|sample 0 1 ty|]
        for value in values do
            let rendered = renderValue ty value
            check ty value rendered
            Assert.Equal<JsonValue>(rendered, Json.serialize rendered |> Json.parse |> take)
            casesExamined <- casesExamined + 1
    Assert.True(casesExamined > 500, sprintf "Incomplete declared-case census: %d" casesExamined)

[<Fact>]
let ``inspection preserves exact wide literals decimal words and every floating bit pattern`` () =
    let literals =
        [ NativeLiteral.Int(Int64.MinValue, NTUKind.NTUint(NTUWidth.Fixed 64))
          NativeLiteral.UInt(UInt64.MaxValue, NTUKind.NTUuint(NTUWidth.Fixed 64))
          NativeLiteral.Decimal Decimal.MaxValue
          NativeLiteral.Decimal(Decimal(0, 0, 0, true, 28uy))
          NativeLiteral.Char(char 0xD800)
          yield! [0L; 1L; Int64.MinValue; 0x7FF0000000000000L; 0x7FF8000000000042L; -4503599627370496L]
                 |> List.map(fun bits -> NativeLiteral.Float(BitConverter.Int64BitsToDouble bits, NTUKind.NTUfloat(NTUWidth.Fixed 64))) ]
    for literal in literals do
        let value = renderValue typeof<NativeLiteral> (box literal)
        check typeof<NativeLiteral> (box literal) value
        Assert.Equal<JsonValue>(value, Json.serialize value |> Json.parse |> take)

[<Fact>]
let ``complete image inspection retains exact proof constants without discharging them`` () =
    let constant = (1I <<< 230) + 9007199254740993I
    let obligation = { Id = "inspection-wide"; Kind = "integer-literal-range"; Logic = "QF_LIA"
                       Statement = "stored premise"; Source = "inspection.clef:1:1"; Refs = []
                       Body = ObligationBody.IntegerLiteralRange(constant, -constant, constant) }
    let revision =
        { Build.bindingWithLiteral with
            CurrentClaims = Map.ofList [NodeId 3, obligation]
            ObligationSources = Map.ofList [NodeId 3, []]
            Obligations = [obligation]; ObligationQuery = "stored-query-is-not-a-discharge" }
    let limits : Binary.Limits = { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128; MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }
    let bytes = Binary.encode limits revision |> take
    let view = Binary.openSource limits (BAREWire.Memory.ByteSource.ofArray bytes) |> take
    let inspected = Inspection.read view |> take |> properties
    Assert.Equal(JsonValue.Bool true, inspected["inspectionOnly"])
    Assert.Equal(int64 revision.Header.Schema, inspected["schema"] |> number)
    Assert.Equal(int64 Binary.FormatVersion, inspected["binaryFormat"] |> number)
    check typeof<Revision> (box revision) inspected["Revision"]
    let text = Inspection.render false view |> take
    Assert.Contains(constant.ToString(CultureInfo.InvariantCulture), text)
    Assert.Contains("stored-query-is-not-a-discharge", text)

[<Fact>]
let ``inspection refuses a partial view whose complete graph has invalid relations`` () =
    let limits : Binary.Limits = { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128; MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let child at index = fst (BAREWire.Encoding.Decoder.readU64 bytes (at + 8 + index * 16)) |> int
    let pointer = child (child (child (child (child (child 64 1) 1) 1) 4) 1) 1
    BAREWire.Encoding.Encoder.writeI32 bytes pointer 999 |> ignore
    let view = Binary.openSource limits (BAREWire.Memory.ByteSource.ofArray bytes) |> take
    match Inspection.read view with
    | Error(BinaryError.InvalidRevision failures) -> Assert.NotEmpty failures
    | other -> failwithf "Inspection admitted or repaired a corrupt graph: %A" other
