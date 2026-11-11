import Segmentation

-- "UAX #29 §3.1.1, revision 49, in the standard's order. First match wins."
-- A dropped, added or reordered row changes which rule decides a position.
theorem «rules lists the sixteen UAX #29 rows in the standard's order» :
    (Segmentation.rules.map (·.name) ==
      ["GB1", "GB2", "GB3", "GB4", "GB5", "GB6", "GB7", "GB8", "GB9", "GB9a", "GB9b",
       "GB9c", "GB11", "GB12", "GB13", "GB999"]) = true := by decide
