namespace Fidelity.PSG.Hosting

open System
open System.IO
open System.IO.MemoryMappedFiles
open BAREWire.Memory
open Fidelity.PSG

[<RequireQualifiedAccess>]
type MappingError =
    | HostFailure of message: string
    | InvalidImage of Binary.Error

/// Owns a read-only mapping of a completed revision image. The publisher must
/// keep the file immutable while readers own it; file sharing is a host lifetime
/// rule, not a source-semantic or proof assertion. Reads and disposal serialize
/// at this boundary. A retained View refuses reads after its owner is disposed.
type MappedRevision private
    (file: FileStream, mapping: MemoryMappedFile, accessor: MemoryMappedViewAccessor,
     gate: obj, view: Binary.View, closeSource: unit -> unit) =
    member _.View = view
    member _.ReadRevision() = lock gate (fun () -> Binary.readRevision view)
    member _.TryNode(identity: NodeId) = lock gate (fun () -> Binary.tryNode identity view)

    interface IDisposable with
        member _.Dispose() =
            lock gate (fun () ->
                closeSource ()
                try accessor.Dispose()
                finally
                    try mapping.Dispose()
                    finally file.Dispose())

    /// Opens an existing, completed image using the same reader as socket bytes.
    /// Opening validates representation only; ReadRevision performs the complete
    /// structural check. Neither operation produces a compiler proof receipt.
    static member Open(limits: Binary.Limits, path: string) : Result<MappedRevision, MappingError> =
        let mutable file: FileStream option = None
        let mutable mapping: MemoryMappedFile option = None
        let mutable accessor: MemoryMappedViewAccessor option = None
        let release () =
            try accessor |> Option.iter (fun value -> value.Dispose())
            finally
                try mapping |> Option.iter (fun value -> value.Dispose())
                finally file |> Option.iter (fun value -> value.Dispose())
        try
            let opened = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read)
            file <- Some opened
            if opened.Length = 0L || opened.Length > int64 limits.MaxBytes then
                release ()
                Error (MappingError.InvalidImage(BinaryError.LimitExceeded("MaxBytes", 0)))
            else
                let mapped = MemoryMappedFile.CreateFromFile(opened, null, 0L, MemoryMappedFileAccess.Read, HandleInheritability.None, true)
                mapping <- Some mapped
                let reader = mapped.CreateViewAccessor(0L, opened.Length, MemoryMappedFileAccess.Read)
                accessor <- Some reader
                let gate = obj ()
                let mutable available = true
                let source = ByteSource.create (uint64 opened.Length) (fun offset count ->
                    lock gate (fun () ->
                        if not available then None
                        else
                            let bytes = Array.zeroCreate<byte> count
                            if reader.ReadArray(int64 offset, bytes, 0, count) = count then Some bytes
                            else None))
                match Binary.openSource limits source with
                | Error error ->
                    release ()
                    Error (MappingError.InvalidImage error)
                | Ok view -> Ok (new MappedRevision(opened, mapped, reader, gate, view, fun () -> available <- false))
        with error ->
            try
                release ()
                Error (MappingError.HostFailure error.Message)
            with cleanup ->
                Error (MappingError.HostFailure(sprintf "%s; mapping cleanup failed: %s" error.Message cleanup.Message))
