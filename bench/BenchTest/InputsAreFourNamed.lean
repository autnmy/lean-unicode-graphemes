import Bench.Inputs

-- "runs both libraries on the same four inputs, generated deterministically from a fixed seed, each named in the results"
theorem «inputs gives four inputs, each with its own non-empty name» :
    (let names := (Bench.inputs 42).map (·.name)
     names.length == 4 && names.all (· != "") && names.eraseDups.length == 4) = true := by
  decide +kernel
