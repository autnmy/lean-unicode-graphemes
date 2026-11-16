import Lean
import Segmentation

-- "No `sorry`, no `implemented_by` or `@[extern]` that the proof does not cover, no `partial def`
-- in the proved path."
open Lean in
/-- breaksBeforeFast is a plain definition, not partial, with no compiled substitute and no
foreign binding, so the code that runs is the code the proof covers. -/
theorem breaks_before_fast_is_plain_with_no_compiled_substitute : True := by
  run_tac do
    let env ← getEnv
    let name := ``Segmentation.breaksBeforeFast
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | some _ => throwError m!"{name} is not a plain definition"
    | none => throwError m!"{name} is missing"
    if (Compiler.getImplementedBy? env name).isSome then
      throwError m!"{name} has a compiled substitute the proof does not cover"
    if isExtern env name then
      throwError m!"{name} is bound to foreign code the proof does not cover"
  trivial
