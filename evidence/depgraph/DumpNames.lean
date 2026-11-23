import Mathlib
/-! Dump the name of every constant in the environment obtained from `import Mathlib`
(Lean core, Std, Batteries, Aesop, Mathlib, ...).  A declaration of the proof export whose
name is NOT in this list was declared by the release itself. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.constants.fold (fun (acc : Array Name) n _ => acc.push n) #[]
  let h ← IO.FS.Handle.mk "mathlib_names.txt" IO.FS.Mode.write
  for n in names do
    h.putStrLn (n.toString false)
  IO.println s!"{names.size} constants written"
