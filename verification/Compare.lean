import Main

/-! Compare separately exported environments using the pinned upstream Comparator. -/

private def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name | throw <| IO.userError s!"Missing {name}"
  return value

#eval show IO Unit from do
  let configText ← IO.FS.readFile (← requiredEnv "COMPARATOR_CONFIG")
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? (α := Comparator.Config)
    (← IO.ofExcept <| Lean.Json.parse configText)
  let mode ← requiredEnv "COMPARATOR_MODE"
  Comparator.M.run (do
    if mode == "targets" then
      let targets := (← Comparator.builtinTargets) ++ (← Comparator.getTheoremNames) ++
        (← Comparator.getLegalAxioms) ++ (← Comparator.primitiveTargets)
      IO.FS.writeFile (← requiredEnv "COMPARATOR_TARGETS")
        (Lean.Json.compress (Lean.toJson (targets.map (·.toString))))
    else if mode == "verify" then
      let reference ← IO.FS.readFile (← requiredEnv "COMPARATOR_REFERENCE_EXPORT")
      let solution ← IO.FS.readFile (← requiredEnv "COMPARATOR_SOLUTION_EXPORT")
      Comparator.verifyMatch reference solution
      IO.println "PASS: reference statement, axiom allowlist, and kernel replay."
    else
      throw <| IO.userError s!"Unknown Comparator mode: {mode}") config
