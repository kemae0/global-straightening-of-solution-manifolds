import GlobalRegularization
import Lean

/-! Validate the manually audited correspondence map. This checks that
anchors still occur on their recorded source lines and that proof references
are actual theorems. It does not automatically translate mathematical prose. -/

open Lean Elab Command in
run_cmd do
  let source ← IO.FS.readFile "manuscript/paper_corrected.tex"
  let raw ← IO.FS.readFile "verification/manuscript-coverage.json"
  let data ← ofExcept (Json.parse raw)
  let claims ← ofExcept (data.getObjValAs? (Array Json) "claims")
  let lines := source.splitOn "\n" |>.toArray
  let env ← getEnv
  let mut ids : Array String := #[]
  let mut count := 0
  for c in claims do
    let id ← ofExcept (c.getObjValAs? String "id")
    if ids.contains id then throwError "Duplicate claim ID: {id}"
    ids := ids.push id
    let line ← ofExcept (c.getObjValAs? Nat "source_line")
    let anchor ← ofExcept (c.getObjValAs? String "anchor")
    unless line > 0 && line ≤ lines.size do throwError "Invalid source line for {id}"
    unless ((lines[line - 1]!).splitOn anchor).length > 1 do
      throwError "Missing source anchor for {id} at line {line}"
    let proofs ← ofExcept (c.getObjValAs? (Array String) "proofs")
    let constructions ← ofExcept (c.getObjValAs? (Array String) "constructions")
    if proofs.isEmpty && constructions.isEmpty then throwError "No certificate for {id}"
    for s in proofs do
      let n := s.toName
      match env.find? n with
      | some (.thmInfo _) => count := count + 1
      | _ => logError m!"Proof reference is not a theorem: {id}: {n}"
    for s in constructions do
      let n := s.toName
      match env.find? n with
      | some (.defnInfo _) => count := count + 1
      | some (.inductInfo _) => count := count + 1
      | _ => logError m!"Construction reference is not a definition/structure: {id}: {n}"
  unless (← get).messages.hasErrors do
    logInfo m!"Coverage references passed: {claims.size} source-anchored claims, {count} theorem/construction references."
