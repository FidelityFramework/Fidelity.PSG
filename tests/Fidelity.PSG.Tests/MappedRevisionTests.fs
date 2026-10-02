module Fidelity.PSG.Tests.MappedRevisionTests

open System
open System.IO
open Xunit
open Fidelity.PSG
open Fidelity.PSG.Hosting

let private limits : Binary.Limits =
    { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
      MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }

let private take = function
    | Ok value -> value
    | Error error -> failwithf "Unexpected mapped-image refusal: %A" error

let private withImage (bytes: byte array) action =
    let path = Path.Combine(Path.GetTempPath(), "psg-mapped-" + Guid.NewGuid().ToString("N") + ".bare")
    try
        File.WriteAllBytes(path, bytes)
        action path
    finally File.Delete path

let private unavailable = function
    | Error(BinaryError.SourceUnavailable _) -> ()
    | other -> failwithf "Disposed source supplied a value or lost its typed lifetime refusal: %A" other

let private exclusive path = new FileStream(path, FileMode.Open, FileAccess.ReadWrite, FileShare.None)

[<Fact>]
let ``mapped array and complete reads preserve authored identities in arbitrary access order`` () =
    let nodes =
        [ { Build.node 41 (SemanticKind.Literal(NativeLiteral.Bool false)) [] with Type = Build.boolType }
          { Build.node 7 (SemanticKind.Literal(NativeLiteral.Bool true)) [] with
              Type = Build.boolType
              Range = { Build.range with File = "mapped-λ.clef"; Start = { Line = 17; Column = 3 }; End = { Line = 17; Column = 7 } } }
          { Build.node 900 (SemanticKind.Literal(NativeLiteral.Bool false)) [] with Type = Build.boolType } ]
    let original = Build.revision nodes
    Assert.Empty(Integrity.check original)
    let bytes = Binary.encode limits original |> take
    withImage bytes (fun path ->
        use mapped = MappedRevision.Open(limits, path) |> take
        let arrayView = Binary.openSource limits (BAREWire.Memory.ByteSource.ofArray bytes) |> take
        let eager = Binary.decode limits bytes |> take
        let complete = mapped.ReadRevision() |> take
        Assert.Equal<Revision>(original, eager)
        Assert.Equal<Revision>(original, complete)
        Assert.Equal<byte>(bytes, Binary.encode limits complete |> take)
        for id in [NodeId 900; NodeId 7; NodeId 41; NodeId 900] do
            Assert.Equal<SemanticNode option>(Some original.Nodes[id], mapped.TryNode id |> take)
            Assert.Equal<SemanticNode option>(Some original.Nodes[id], Binary.tryNode id arrayView |> take)
        Assert.Equal<SemanticNode option>(None, mapped.TryNode(NodeId 1001) |> take)
        Assert.Equal<byte>(bytes, File.ReadAllBytes path))

[<Fact>]
let ``mapped lifetime owns file lease and retained views refuse after disposal`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    withImage bytes (fun path ->
        use mapped = MappedRevision.Open(limits, path) |> take
        let view = mapped.View
        Assert.ThrowsAny<IOException>(fun () -> use premature = exclusive path in ()) |> ignore
        Assert.Equal<SemanticNode option>(Some Build.bindingWithLiteral.Nodes[NodeId 2], mapped.TryNode(NodeId 2) |> take)
        (mapped :> IDisposable).Dispose()
        Binary.tryNode (NodeId 2) view |> unavailable
        Binary.readRevision view |> unavailable
        mapped.TryNode(NodeId 2) |> unavailable
        mapped.ReadRevision() |> unavailable
        (mapped :> IDisposable).Dispose()
        use released = exclusive path
        Assert.Equal(int64 bytes.Length, released.Length))

[<Fact>]
let ``failed truncated corrupt or over-budget open immediately releases its file lease`` () =
    let valid = Binary.encode limits Build.bindingWithLiteral |> take
    let badMagic = Array.copy valid
    badMagic[0] <- 0uy
    let badContract = Array.copy valid
    badContract[16] <- badContract[16] ^^^ 255uy
    let cases =
        [ limits, [||]
          limits, valid[..62]
          limits, valid[..valid.Length - 2]
          limits, Array.append valid [|0uy|]
          limits, badMagic
          limits, badContract
          { limits with MaxBytes = valid.Length - 1; MaxStringBytes = 0; MaxBigIntegerBytes = 0 }, valid ]
    for bounds, bytes in cases do
        withImage bytes (fun path ->
            match MappedRevision.Open(bounds, path) with
            | Error(MappingError.InvalidImage _) -> ()
            | Error error -> failwithf "Representation refusal became a host failure: %A" error
            | Ok unexpected ->
                (unexpected :> IDisposable).Dispose()
                failwith "Malformed or over-budget image was admitted"
            // No GC or finalizer can stand in for failed-construction cleanup.
            use released = exclusive path
            Assert.Equal(int64 bytes.Length, released.Length))

[<Fact>]
let ``opening a node index grants neither complete structural admission nor repaired references`` () =
    let bytes = Binary.encode limits Build.bindingWithLiteral |> take
    let child at index =
        let offset, _ = BAREWire.Encoding.Decoder.readU64 bytes (at + 8 + index * 16)
        int offset
    let nodes = child 64 1
    let entry = child nodes 1
    let node = child entry 1
    let children = child node 4
    let childId = child children 1
    let childValue = child childId 1
    BAREWire.Encoding.Encoder.writeI32 bytes childValue 999 |> ignore
    withImage bytes (fun path ->
        use mapped = MappedRevision.Open(limits, path) |> take
        // A valid sibling remains individually readable. The complete graph
        // must still refuse the dangling relation; no node is renumbered.
        Assert.Equal<SemanticNode option>(Some Build.bindingWithLiteral.Nodes[NodeId 2], mapped.TryNode(NodeId 2) |> take)
        match mapped.ReadRevision() with
        | Error(BinaryError.InvalidRevision failures) -> Assert.NotEmpty failures
        | other -> failwithf "Corrupt references were admitted or repaired: %A" other
        Assert.Equal<byte>(bytes, File.ReadAllBytes path))

// Images are completed and immutable for the mapping's lifetime by the
// publisher/host contract. FileShare.Read excludes cooperating .NET writers;
// it is not a proof of immutability against arbitrary external file mutation.
// Neither Open, a successful indexed read, nor a matching hash grants source
// freshness, proof discharge, or execution authority.
