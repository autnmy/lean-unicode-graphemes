import Segmentation

open Segmentation Segmentation.Tables in
theorem «props reads every property through the linear scan of its table for every Char» :
    ∀ c : Char, props c =
      { gcb := Range.scan GCB.Other gcbRanges c.toNat,
        extPict := Range.scan false extPictRanges c.toNat,
        incb := Range.scan InCB.None incbRanges c.toNat } :=
  props_eq_scan
