import Segmentation

-- GB3 (CR × LF) comes before GB4 (break after CR) in Segmentation.rules. Stub lookup: '\r' is CR,
-- '\n' is LF. The first CR is followed by a CR, so GB4 breaks; the second CR is followed by LF,
-- so GB3 joins. Expected clusters: [CR], [CR LF].
set_option maxRecDepth 20000 in
theorem «clustersOf joins CR LF but keeps a lone CR before it apart (GB3 against GB4)» :
    Segmentation.clustersOf
      (fun c =>
        if c = '\r' then { gcb := .CR, extPict := false, incb := .None }
        else if c = '\n' then { gcb := .LF, extPict := false, incb := .None }
        else { gcb := .Other, extPict := false, incb := .None })
      ['\r', '\r', '\n'] =
    [['\r'], ['\r', '\n']] := by
  decide
