import Std
import Leaf.Core.Types
import Leaf.Core.Policy

namespace Leaf

open Leaf.Core

structure Draft where
  author  : String := "journal"
  title   : Option String := none
  caption : String := ""
  image   : ByteArray := ByteArray.empty
  deriving Inhabited

structure EditDraft where
  author?     : Option String := none
  title?      : Option (Option String) := none
  caption?    : Option String := none
  removeImage : Bool := false
  image?      : Option ByteArray := none
  deriving Inhabited

def imageType (b : ByteArray) : Option String :=
  (detectMimeType b).map MimeType.toString

private def atBytes (b token : ByteArray) (i : Nat) : Bool :=
  i + token.size <= b.size && (b.extract i (i + token.size)).data == token.data

private def locate (b token : ByteArray) (start stop : Nat) (delimiter := false) : Option Nat := Id.run do
  for i in [start:min stop b.size] do
    if b[i]! == token[0]! && atBytes b token i then
      let j := i + token.size
      if !delimiter || atBytes b "\r\n".toUTF8 j || atBytes b "--".toUTF8 j then
        return some i
  return none

private def parseMultipartFields (contentType : String) (body : ByteArray) :
    Except String (Array (String × ByteArray)) := do
  let parts := contentType.splitOn ";"
  let media := (parts.head?.map (fun s => s.trimAscii.toString)).getD ""
  let param := (parts.tail.find? (fun s => s.trimAscii.toString.startsWith "boundary=")).getD ""
  let p := param.trimAscii.toString
  unless media == "multipart/form-data" && p.startsWith "boundary=" do
    throw "Expected a multipart form."
  let key := ((p.drop 9).toString.replace "\"" "")
  unless key.length > 0 && key.length <= 70 do throw "Invalid boundary."
  let first := ("--" ++ key ++ "\r\n").toUTF8
  let marker := ("\r\n--" ++ key).toUTF8
  unless atBytes body first 0 do throw "Invalid form."
  let mut pos := first.size
  let mut out : Array (String × ByteArray) := #[]
  for _ in [0:12] do
    let some h := locate body "\r\n\r\n".toUTF8 pos (pos + 4096) | throw "Invalid part headers."
    let some headers := String.fromUTF8? (body.extract pos h) | throw "Invalid part headers."
    let some disp := (headers.splitOn "\r\n").find? (·.startsWith "Content-Disposition: form-data;")
      | throw "Missing disposition."
    let params := (disp.splitOn ";").map (fun s => s.trimAscii.toString)
    let some field := params.find? (·.startsWith "name=") | throw "Missing field."
    let fieldName := (field.drop 5).toString.replace "\"" ""
    let some e := locate body marker (h + 4) body.size true | throw "Incomplete upload."
    let value := body.extract (h + 4) e
    out := out.push (fieldName, value)
    pos := e + marker.size
    if atBytes body "--".toUTF8 pos then
      unless body.size == pos + 2 || (body.size == pos + 4 && atBytes body "\r\n".toUTF8 (pos + 2)) do
        throw "Invalid form ending."
      return out
    pos := pos + 2
  throw "Too many fields."

def parseForm (contentType : String) (body : ByteArray)
    (maxImageBytes : Nat := StoragePolicy.default.maxImageBytes) : Except String Draft := do
  let fields ← parseMultipartFields contentType body
  let mut draft : Draft := {}
  for (name, value) in fields do
    if name == "author" then
      let some a := String.fromUTF8? value | throw "Invalid author."
      let t := a.trimAscii.toString
      if !t.isEmpty then
        draft := { draft with author := t }
    else if name == "title" then
      let some t := String.fromUTF8? value | throw "Invalid title."
      let trimmed := t.trimAscii.toString
      draft := { draft with title := if trimmed.isEmpty then none else some trimmed }
    else if name == "caption" then
      let some caption := String.fromUTF8? value | throw "Invalid caption."
      if caption.length > 500 then throw "Use at most 500 characters."
      draft := { draft with caption := caption.trimAscii.toString }
    else if name == "image" then
      if value.size > maxImageBytes then throw "Image exceeds maximum allowed size."
      if value.size > 0 && (detectMimeType value).isNone then
        throw "Choose a JPEG, PNG, WebP, or GIF image."
      draft := { draft with image := value }
  if draft.caption.isEmpty && draft.image.size == 0 then
    throw "Add a caption or an image."
  return draft

def parseEditForm (contentType : String) (body : ByteArray)
    (maxImageBytes : Nat := StoragePolicy.default.maxImageBytes) : Except String EditDraft := do
  let fields ← parseMultipartFields contentType body
  let mut edit : EditDraft := {}
  for (name, value) in fields do
    if name == "author" then
      let some a := String.fromUTF8? value | throw "Invalid author."
      let t := a.trimAscii.toString
      if !t.isEmpty then
        edit := { edit with author? := some t }
    else if name == "title" then
      let some t := String.fromUTF8? value | throw "Invalid title."
      let trimmed := t.trimAscii.toString
      edit := { edit with title? := some (if trimmed.isEmpty then none else some trimmed) }
    else if name == "caption" then
      let some c := String.fromUTF8? value | throw "Invalid caption."
      if c.length > 500 then throw "Use at most 500 characters."
      edit := { edit with caption? := some c.trimAscii.toString }
    else if name == "remove_image" then
      let some v := String.fromUTF8? value | throw "Invalid remove_image flag."
      if v.trimAscii.toString == "1" || v.trimAscii.toString == "on" then
        edit := { edit with removeImage := true }
    else if name == "image" then
      if value.size > maxImageBytes then throw "Image exceeds maximum allowed size."
      if value.size > 0 then
        if (detectMimeType value).isNone then
          throw "Choose a JPEG, PNG, WebP, or GIF image."
        edit := { edit with image? := some value }
  return edit

end Leaf
