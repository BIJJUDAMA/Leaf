import Lean

namespace Leaf
open Lean System

structure Post where
  id : Nat
  caption : String
  created : String
  mime : Option String
  deriving ToJson, FromJson, Inhabited

/-- Rows are ordered by their unique primary key. -/
structure Database where
  version : Nat
  posts : Array Post
  deriving ToJson, FromJson, Inhabited

namespace Database

def nextId (db : Database) : Nat := (db.posts.back?.map (·.id)).getD 0 + 1

def lookup (db : Database) (id : Nat) : Option Post :=
  db.posts.binSearch { (default : Post) with id } (fun a b => a.id < b.id)

def read (path : FilePath) : IO Database := do
  let db : Database ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)
  unless db.version == 1 do throw <| IO.userError "Unsupported Leaf database version"
  let mut last : Option Nat := none
  for row in db.posts do
    if last.any (· >= row.id) then throw <| IO.userError "Invalid post key order"
    last := some row.id
  return db

def commit (db : Database) (path : FilePath) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp (toJson db).compress
  IO.FS.rename tmp path

end Database
end Leaf
