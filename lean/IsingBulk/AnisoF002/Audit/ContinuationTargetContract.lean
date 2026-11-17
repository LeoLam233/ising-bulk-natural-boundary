import IsingBulk.AnisoF002.TargetSpec
import IsingBulk.AnisoF002.Audit.PinnedStatement
import IsingBulkAnisoF002Continuation
import IsingBulk.AnisoF002.Audit.RouteCheck

/-!
This executable contract check compares the compiled proposition body with
the literal required type.  The check does not create a proof of the target.
It explicitly reports whether the required terminal theorem is absent.
-/

open Lean Elab Command Term Meta
open IsingBulk.Anisotropic
open IsingBulk.Anisotropic.FormFactors IsingBulk.Anisotropic.PhysicalField

run_cmd do
  let expected ← liftTermElabM do
    elabTerm (← `(∀ {J lam : ℝ}, 0 < J → 0 < lam →
      ∀ {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
        PublishedRealSpinFormFactors lam corrH corrL →
        PublishedRealGibbsFields J lam corrH corrL mH mL →
        FullUniformFieldConclusion J lam corrH corrL mH mL))
      (some (mkSort .zero))
  let env ← getEnv
  let some (.defnInfo specification) := env.checked.get.find? `IsingBulk.AnisoF002.RequiredStatement
    | throwError "F002_TARGET_SPEC_MISSING_DEFINITION"
  let same ← liftTermElabM <| isDefEq specification.value expected
  unless same do throwError "F002_TARGET_SPEC_WRONG_TYPE"
  let some (.defnInfo frozen) := env.checked.get.find? `IsingBulk.AnisoF002.Audit.FrozenTerminalStatement
    | throwError "F002_FROZEN_SIGNATURE_MISSING_DEFINITION"
  let sameFrozen ← liftTermElabM <| isDefEq specification.value frozen.value
  unless sameFrozen do throwError "F002_TARGET_DIFFERS_FROM_FROZEN_ORIGINAL_SIGNATURE"
  logInfo "F002_TARGET_MATCHES_FROZEN_ORIGINAL_SIGNATURE"
  logInfo m!"F002_EXACT_TARGET_SPEC_CHECKED: {specification.value}"
  match env.checked.get.find? `IsingBulk.AnisoF002.full_uniform_field_conclusion with
  | none =>
    logInfo "F002_TERMINAL_THEOREM_OPEN: no stored proof of full_uniform_field_conclusion is declared"
  | some info =>
    unless info.isTheorem do throwError "F002_TERMINAL_IS_NOT_THEOREM"
    let same ← liftTermElabM <| isDefEq info.type expected
    unless same do throwError "F002_TERMINAL_THEOREM_WRONG_TYPE"
    logInfo "F002_TERMINAL_TYPE_MATCHES: separate stored-proof route audit still required"
  match env.checked.get.find? `IsingBulk.AnisoF002.full_analytic_conclusion with
  | none =>
    logInfo "F002_ANALYTIC_THEOREM_OPEN: no stored proof of full_analytic_conclusion is declared"
  | some info =>
    unless info.isTheorem do throwError "F002_ANALYTIC_IS_NOT_THEOREM"
    let some (.defnInfo analytical) := env.checked.get.find? `IsingBulk.AnisoF002.RequiredAnalyticStatement
      | throwError "F002_ANALYTIC_SPEC_MISSING_DEFINITION"
    let same ← liftTermElabM <| isDefEq info.type analytical.value
    unless same do throwError "F002_ANALYTIC_THEOREM_WRONG_TYPE"
    logInfo "F002_ANALYTIC_TYPE_MATCHES: separate stored-proof route audit still required"
