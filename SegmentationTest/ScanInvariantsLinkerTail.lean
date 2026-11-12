import Segmentation

open Segmentation

def scanInvLinker : Props := { gcb := .Extend, extPict := false, incb := .Linker }
def scanInvLinkerNone : Props := { gcb := .Other, extPict := false, incb := .None }
def scanInvLinkerExtend : Props := { gcb := .Extend, extPict := false, incb := .Extend }

-- "Linker then an InCB None code point gives `linkerTail = false`"
-- The Linker, Extend case pins that the flag survives InCB Extend.
theorem «Linker then InCB None leaves linkerTail false but Linker Extend keeps it» :
    (scanStateOf scanInvLinker [scanInvLinkerNone]).linkerTail = false ∧
    (scanStateOf scanInvLinker [scanInvLinkerExtend]).linkerTail = true := by
  decide
