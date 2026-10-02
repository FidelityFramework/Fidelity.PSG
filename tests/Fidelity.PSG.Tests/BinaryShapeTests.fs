module Fidelity.PSG.Tests.BinaryShapeTests

open System
open System.Collections
open System.Reflection
open Microsoft.FSharp.Reflection
open Xunit
open Fidelity.PSG
open Fidelity.PSG.Tests.BinaryTests

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

// Compare every field independently of generated serialization, including float
// and decimal bit patterns. NoEquality records remain fully examined.
let rec private describe (ty: Type) (value: obj) : string =
    if ty = typeof<float> then sprintf "f64:%016X" (BitConverter.DoubleToInt64Bits(unbox value))
    elif ty = typeof<decimal> then Decimal.GetBits(unbox value) |> Array.map (sprintf "%08X") |> String.concat ":"
    elif ty = typeof<string> then sprintf "%A" (unbox<string> value)
    elif ty.IsPrimitive || ty = typeof<bigint> then sprintf "%A" value
    elif FSharpType.IsTuple ty then
        Array.map2 describe (FSharpType.GetTupleElements ty) (FSharpValue.GetTupleFields value) |> String.concat "," |> sprintf "(%s)"
    elif ty.IsArray then
        (value :?> IEnumerable) |> Seq.cast<obj> |> Seq.map (describe (ty.GetElementType())) |> String.concat ";" |> sprintf "[%s]"
    elif (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpMap`" then
        let args = ty.GetGenericArguments()
        (value :?> IEnumerable) |> Seq.cast<obj> |> Seq.map(fun item ->
            let itemType = item.GetType()
            describe args[0] (itemType.GetProperty("Key").GetValue item) + "=" + describe args[1] (itemType.GetProperty("Value").GetValue item))
        |> String.concat ";" |> sprintf "map[%s]"
    elif (generic ty).StartsWith "Microsoft.FSharp.Collections.FSharpSet`" then
        (value :?> IEnumerable) |> Seq.cast<obj> |> Seq.map (describe (ty.GetGenericArguments()[0])) |> String.concat ";" |> sprintf "set[%s]"
    elif FSharpType.IsRecord(ty, flags) then
        Array.map2 (fun (field: PropertyInfo) item -> field.Name + "=" + describe field.PropertyType item)
            (FSharpType.GetRecordFields(ty, flags)) (FSharpValue.GetRecordFields(value, flags))
        |> String.concat ";" |> sprintf "%s{%s}" ty.FullName
    elif FSharpType.IsUnion(ty, flags) then
        let case, fields = FSharpValue.GetUnionFields(value, ty, flags)
        Array.map2 (fun (field: PropertyInfo) item -> describe field.PropertyType item) (case.GetFields()) fields
        |> String.concat "," |> sprintf "%s.%s(%s)" ty.FullName case.Name
    else failwithf "No independent comparison for %s" ty.FullName

[<Fact>]
let ``every generated record and every declared DU constructor roundtrips all its fields`` () =
    let owner = typeof<BinaryIndexed.WriteState>.DeclaringType.FullName
    let generated = typeof<BinaryIndexed.WriteState>.Assembly.GetType(owner.Replace("BinaryIndexed", "BinaryGenerated"), true)
    let writers = generated.GetMethods(BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static)
                  |> Array.filter(fun methodInfo ->
                      let parameters = methodInfo.GetParameters()
                      methodInfo.Name.StartsWith("write_", StringComparison.Ordinal)
                      && parameters.Length = 2 && parameters[0].ParameterType = typeof<BinaryIndexed.WriteState>)
    Assert.Equal(BinaryGenerated.NamedTypes, writers.Length)
    let mutable casesExamined = 0
    for writer in writers do
        let ty = (writer.GetParameters()).[1].ParameterType
        let reader = generated.GetMethod("read_" + writer.Name.Substring(6), BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static)
        let values =
            if FSharpType.IsUnion(ty, flags) then
                FSharpType.GetUnionCases(ty, flags) |> Array.map(fun case ->
                    let fields = case.GetFields() |> Array.mapi(fun at field -> sample 0 (at + case.Tag + 1) field.PropertyType)
                    FSharpValue.MakeUnion(case, fields, flags))
            else [|sample 0 1 ty|]
        for original in values do
            let state = writer.Invoke(null, [|box (BinaryIndexed.initialWrite limits); original|]) :?> Result<BinaryIndexed.WriteState, BinaryError> |> take
            let fragment = BinaryIndexed.fragment state |> take
            let bytes = Array.zeroCreate (BinaryIndexed.size fragment)
            BinaryIndexed.writeFragment bytes 0 fragment
            let source = BAREWire.Memory.ByteSource.ofArray bytes
            let location : BinaryIndexed.Location = { Offset = 0UL; Length = uint64 bytes.Length }
            let result = reader.Invoke(null, [|box (BinaryIndexed.initialRead limits source location)|])
            let resultCase, resultFields = FSharpValue.GetUnionFields(result, result.GetType(), flags)
            Assert.True((resultCase.Name = "Ok"), sprintf "%s refused: %A" ty.FullName result)
            let decoded = (FSharpValue.GetTupleFields(resultFields[0])).[0]
            Assert.Equal(describe ty original, describe ty decoded)
            casesExamined <- casesExamined + 1
    Assert.True(casesExamined > 500, sprintf "Unexpectedly narrow case census: %d" casesExamined)
