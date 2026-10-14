import PrimeSphericalFoldComplete
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of every declaration owned by this companion. -/

#check PrimeSphericalFold.complete_geometry

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun name =>
    name.toString.startsWith "PrimeSphericalFold." ||
      name.toString.startsWith "_private.PrimeSphericalFold"
  if names.isEmpty then
    throwError "No companion declarations found"
  let names := names.mergeSort Name.quickLt
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"PASS: {names.length} companion declarations; only propext, Classical.choice, Quot.sound allowed"
