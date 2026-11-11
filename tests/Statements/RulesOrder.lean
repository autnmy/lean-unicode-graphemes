import Segmentation

-- "UAX #29 §3.1.1, revision 49, in the standard's order. First match wins."
-- Because the first matching rule decides, a dropped or reordered row changes what
-- IsBoundary means, so the full name list is pinned here.
theorem «rules lists GB1 to GB999 in the standard's order with no row dropped or moved» :
    Segmentation.rules.map (·.name) =
      ["GB1", "GB2", "GB3", "GB4", "GB5", "GB6", "GB7", "GB8", "GB9", "GB9a", "GB9b",
       "GB9c", "GB11", "GB12", "GB13", "GB999"] := rfl
