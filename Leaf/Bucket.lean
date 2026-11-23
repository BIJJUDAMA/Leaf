import Std

namespace Leaf
open System

structure Bucket where
  directory : FilePath

namespace Bucket

def openAt (path : FilePath) : IO Bucket := do
  IO.FS.createDirAll path
  return ⟨path⟩

def put (bucket : Bucket) (id : Nat) (bytes : ByteArray) : IO Unit := do
  let tmp := bucket.directory / "upload.tmp"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp (bucket.directory / toString id)

def get (bucket : Bucket) (id : Nat) : IO ByteArray :=
  IO.FS.readBinFile (bucket.directory / toString id)

end Bucket
end Leaf