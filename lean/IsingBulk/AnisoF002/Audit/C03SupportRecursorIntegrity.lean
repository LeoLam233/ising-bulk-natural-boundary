import IsingBulk.AnisoF002.C03.RegularMatching
import IsingBulk.AnisoF002.C03.IsotropicUniformJets
import IsingBulk.AnisoF002.Audit.C03SupportPolicy

/-!
The five explicitly noncomputable recursors retain their original checked
logical types and stored values. Their executable partial companions must
be absent. No exception to the logical partial/unsafe check is introduced.
The complete before/after elaborated terms are preserved in audit evidence.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let expected : Array (Name × UInt64 × UInt64) := #[
    (`IsingBulk.AnisoF002.RegularTail.C03.pairProductOn, 150906652, 1077002858),
    (`IsingBulk.AnisoF002.RegularTail.C03.pfaffianOn, 2666848261, 2087107821),
    (`IsingBulk.AnisoF002.RegularTail.C03.matchedExpansion, 2164801013, 1672892292),
    (`IsingBulk.AnisoF002.RegularTail.C03.matchingNumber, 2546708756, 475305119),
    (`IsingBulk.AnisoF002.Isotropic.protectedJetConstant, 869665623, 2852690132)]
  let mut rows : Array Json := #[]
  for (name, typeHash, valueHash) in expected do
    let some info := env.checked.get.find? name
      | throwError "C03_RECURSOR_MISSING: {name}"
    unless info.isDefinition && !info.isUnsafe && !info.isPartial do
      throwError "C03_RECURSOR_NOT_SAFE_DEFINITION: {name}"
    let some value := info.value? true
      | throwError "C03_RECURSOR_VALUE_MISSING: {name}"
    unless info.type.hash == typeHash && value.hash == valueHash do
      throwError "C03_RECURSOR_LOGICAL_FINGERPRINT_CHANGED: {name}"
    let companion := Compiler.mkUnsafeRecName name
    if (env.checked.get.find? companion).isSome then
      throwError "C03_EXECUTION_COMPANION_REMAINS: {companion}"
    let fullType ← liftTermElabM <| withOptions (fun o => o.setBool `pp.all true) do
      return (← Meta.ppExpr info.type).pretty 180
    let fullValue ← liftTermElabM <| withOptions (fun o => o.setBool `pp.all true) do
      return (← Meta.ppExpr value).pretty 180
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("type", toJson fullType),
      ("value", toJson fullValue), ("type_hash", toJson (toString info.type.hash)),
      ("value_hash", toJson (toString value.hash)),
      ("execution_companion_absent", toJson true)]
    logInfo m!"C03_RECURSOR_UNCHANGED_AND_COMPANION_ABSENT: {name}"
  IO.FS.writeFile "../evidence/support_c03/runtime_recursors_after.json" (toJson rows).pretty
  logInfo "C03_RECURSOR_INTEGRITY_PASS"
