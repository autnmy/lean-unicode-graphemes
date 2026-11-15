import Segmentation

-- GB3 (CR × LF) comes before GB4 (break after CR) in Segmentation.rules. Stub lookup: '\r' is CR,
-- '\n' is LF. The first CR is followed by a CR, so GB4 breaks; the second CR is followed by LF,
-- so GB3 joins. Expected clusters: [CR], [CR LF].
set_option maxRecDepth 20000 in
theorem «clustersOf joins CR LF but keeps a lone CR before it apart (GB3 against GB4)» :
    Segmentation.clustersOf
      (fun c =>
        if c = '\r' then { gcb := .cr, extPict := false, incb := .none }
        else if c = '\n' then { gcb := .lf, extPict := false, incb := .none }
        else { gcb := .other, extPict := false, incb := .none })
      ['\r', '\r', '\n'] =
    [['\r'], ['\r', '\n']] := by
  decide
