import Main

-- `measure fast <input>` parses to a measurement of the fast library, because `Library` gains a
-- `.fast` case named "fast" in `Library.all` and `Library.name`; an unknown library name still
-- fails to parse.
#guard
    ((match Bench.parseCommand ["measure", "fast", "emoji"] with
      | some (.measure .fast _) => true
      | _ => false) &&
     (Bench.Library.all.contains .fast) &&
     (Bench.Library.name .fast == "fast") &&
     (Bench.parseCommand ["measure", "quick", "emoji"]).isNone)
