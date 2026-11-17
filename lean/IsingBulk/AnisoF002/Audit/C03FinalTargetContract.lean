import IsingBulk.AnisoF002.C03.FullUniformFieldConclusion
import IsingBulk.AnisoF002.Audit.PinnedStatement
import IsingBulk.AnisoF002.TargetSpec
import Lean

/-!
# Additive final target and original physical-scope contract

This driver requires the stored terminal theorem, after importing its actual
source. It independently compares the literal original signature, every
conclusion field, both original physical structures and the Gibbs entry
structure. It does not replace the separate transitive route/axiom audit or
the official fresh kernel replay. The recovered contract modules are unchanged.
-/

namespace IsingBulk.AnisoF002.Audit
open Lean Elab Command Term Meta
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open IsingBulk.Anisotropic.PhysicalField
open Set Filter
open scoped Topology BigOperators

set_option pp.all true

def c03CheckType (name : Name) (expectedSyntax : Syntax) : CommandElabM Unit := do
  let some info := (← getEnv).checked.get.find? name
    | throwError "F002_FINAL_CONTRACT_MISSING_CONSTANT: {name}"
  liftTermElabM do
    let expected ← elabTerm expectedSyntax (some (← inferType info.type))
    synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq info.type expected do
      throwError "F002_FINAL_CONTRACT_FIELD_TYPE_MISMATCH: {name}; actual={info.type}; expected={expected}"
  logInfo m!"F002_FINAL_CONTRACT_EXACT_TYPE: {name}; {info.type}"

def c03CheckDefinition (name : Name) (expectedSyntax : Syntax) : CommandElabM Unit := do
  let some (.defnInfo info) := (← getEnv).checked.get.find? name
    | throwError "F002_FINAL_CONTRACT_MISSING_DEFINITION: {name}"
  liftTermElabM do
    let expected ← elabTerm expectedSyntax (some info.type)
    synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq info.value expected do
      throwError "F002_FINAL_CONTRACT_DEFINITION_MISMATCH: {name}; actual={info.value}; expected={expected}"
  logInfo m!"F002_FINAL_CONTRACT_EXACT_BODY: {name}; {info.value}"

def c03CheckFields (name : Name) (fields : Array Name) : CommandElabM Unit := do
  let some info := getStructureInfo? (← getEnv) name
    | throwError "F002_FINAL_CONTRACT_NOT_STRUCTURE: {name}"
  unless info.fieldNames == fields do
    throwError "F002_FINAL_CONTRACT_EXTRA_OR_MISSING_FIELDS: {name}; {info.fieldNames}"
  unless info.parentInfo.isEmpty do
    throwError "F002_FINAL_CONTRACT_HIDDEN_PARENT: {name}"
  logInfo m!"F002_FINAL_CONTRACT_EXACT_FIELDS: {name}; {info.fieldNames}"

def c03ForallBinders (expr : Expr) : Array (Name × BinderInfo) := Id.run do
  let mut cursor := expr
  let mut result := #[]
  while true do
    match cursor with
    | .forallE name _ body bi =>
      result := result.push (name, bi)
      cursor := body
    | _ => return result
  return result

def c03ReplaceConclusion (expr conclusion : Expr) : Expr := Id.run do
  let mut cursor := expr
  let mut binders : Array (Name × Expr × BinderInfo) := #[]
  while cursor.isForall do
    match cursor with
    | .forallE name domain body bi =>
      binders := binders.push (name, domain, bi)
      cursor := body
    | _ => pure ()
  return binders.foldr (fun (name, domain, bi) body => .forallE name domain body bi) conclusion

run_cmd do
  let env ← getEnv
  let some (.thmInfo terminal) := env.checked.get.find?
      `IsingBulk.AnisoF002.full_uniform_field_conclusion
    | throwError "F002_FINAL_STORED_TERMINAL_THEOREM_REQUIRED"
  let some (.defnInfo required) := env.checked.get.find? `IsingBulk.AnisoF002.RequiredStatement
    | throwError "F002_FINAL_ORIGINAL_REQUIRED_STATEMENT_MISSING"
  let some (.defnInfo frozen) := env.checked.get.find? `IsingBulk.AnisoF002.Audit.FrozenTerminalStatement
    | throwError "F002_FINAL_FROZEN_SIGNATURE_MISSING"
  let expected ← liftTermElabM do
    elabTerm (← `(∀ {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam)
      {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL →
      PublishedRealGibbsFields J lam corrH corrL mH mL →
      FullUniformFieldConclusion J lam corrH corrL mH mL)) (some (mkSort .zero))
  for candidate in [terminal.type, required.value, frozen.value] do
    unless ← liftTermElabM <| isDefEq candidate expected do
      throwError "F002_FINAL_EXACT_ORIGINAL_SIGNATURE_MISMATCH"
  unless c03ForallBinders terminal.type == c03ForallBinders frozen.value do
    throwError "F002_FINAL_BINDER_ORDER_NAMES_OR_IMPLICITNESS_CHANGED"
  let valueType ← liftTermElabM <| inferType terminal.value
  unless ← liftTermElabM <| isDefEq valueType expected do
    throwError "F002_FINAL_STORED_VALUE_HAS_WRONG_TYPE"
  logInfo m!"F002_FINAL_STORED_TERMINAL_EXACT: {terminal.type}"
  logInfo m!"F002_FINAL_STORED_TERMINAL_VALUE: {terminal.value}"
  logInfo m!"F002_FINAL_EXACT_BINDERS: {reprStr (c03ForallBinders terminal.type)}"
  let impossible := mkForall `artificialFalse .default (mkConst ``False) expected
  let weakened := c03ReplaceConclusion expected (mkConst ``True)
  let restricted ← liftTermElabM do
    elabTerm (← `(∀ {J lam : ℝ}, 0 < J → 0 < lam → lam ≠ 1 →
      ∀ {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL →
      PublishedRealGibbsFields J lam corrH corrL mH mL →
      FullUniformFieldConclusion J lam corrH corrL mH mL)) (some (mkSort .zero))
  for (tag, bad) in [("impossible_extra_premise", impossible), ("weakened_conclusion", weakened),
      ("isotropic_exclusion", restricted)] do
    if ← liftTermElabM <| isDefEq terminal.type bad then
      throwError "F002_FINAL_NEGATIVE_TYPE_CONTROL_ACCEPTED: {tag}"
    logInfo m!"F002_FINAL_NEGATIVE_TYPE_CONTROL_REJECTED: {tag}"

run_cmd do
  c03CheckDefinition `IsingBulk.Anisotropic.FullUniformFieldConclusion
    (← `(fun (J lam : ℝ) (corrH corrL : ℝ → LatticeSite → ℝ) (mH mL : ℝ → ℝ → ℝ) =>
      FullPhysicalConclusion J lam corrH corrL ∧ RealUniformFieldIdentification J lam corrH corrL mH mL))
  c03CheckDefinition `IsingBulk.Anisotropic.FullPhysicalConclusion
    (← `(fun (J lam : ℝ) (corrH corrL : ℝ → LatticeSite → ℝ) =>
      FullAnalyticConclusion J lam ∧ RealPhysicalIdentification J lam corrH corrL))
  c03CheckDefinition `IsingBulk.Anisotropic.FullAnalyticConclusion
    (← `(fun (J lam : ℝ) =>
      NaturalBoundaryOn (omegaH lam) (highNormalizedBulk lam) ∧
      NaturalBoundaryOn (omegaL lam) (lowNormalizedBulk lam) ∧
      NaturalBoundaryOn (omegaH lam) (highPhysicalBulk J lam) ∧
      NaturalBoundaryOn (omegaL lam) (lowPhysicalBulk J lam)))
  c03CheckDefinition `IsingBulk.Anisotropic.NaturalBoundaryOn
    (← `(fun (D : Set ℂ) (f : ℂ → ℂ) => AnalyticOnNhd ℂ f D ∧
      ∀ z ∈ frontier D, ¬ HasDomainExtension D f z))
  c03CheckDefinition `IsingBulk.Anisotropic.HasDomainExtension
    (← `(fun (D : Set ℂ) (f : ℂ → ℂ) (z : ℂ) =>
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g U ∧ EqOn g f (U ∩ D)))
  c03CheckDefinition `IsingBulk.Anisotropic.highPhysicalBulk
    (← `(fun (J lam : ℝ) => inverseTemperature J * highNormalizedBulk lam))
  c03CheckDefinition `IsingBulk.Anisotropic.lowPhysicalBulk
    (← `(fun (J lam : ℝ) => inverseTemperature J * lowNormalizedBulk lam))
  c03CheckDefinition `IsingBulk.Anisotropic.inverseTemperature
    (← `(fun (J : ℝ) (z : ℂ) => z / (2 * (J : ℂ))))
  c03CheckDefinition `IsingBulk.Anisotropic.FormFactors.highCovarianceSum
    (← `(fun (corrH : ℝ → LatticeSite → ℝ) (x : ℝ) => ∑' v : LatticeSite, corrH x v))
  c03CheckDefinition `IsingBulk.Anisotropic.FormFactors.lowCovarianceSum
    (← `(fun (lam : ℝ) (corrL : ℝ → LatticeSite → ℝ) (x : ℝ) =>
      ∑' v : LatticeSite, (corrL x v - realMagnetizationSq lam x)))
  c03CheckDefinition `IsingBulk.Anisotropic.FormFactors.highEnergyFieldResponse
    (← `(fun (J : ℝ) (corrH : ℝ → LatticeSite → ℝ) (x : ℝ) =>
      (x / (2 * J)) * highCovarianceSum corrH x))
  c03CheckDefinition `IsingBulk.Anisotropic.FormFactors.lowEnergyFieldResponse
    (← `(fun (J lam : ℝ) (corrL : ℝ → LatticeSite → ℝ) (x : ℝ) =>
      (x / (2 * J)) * lowCovarianceSum lam corrL x))

run_cmd do
  c03CheckFields `IsingBulk.Anisotropic.RealPhysicalIdentification #[`high, `low]
  c03CheckType `IsingBulk.Anisotropic.RealPhysicalIdentification.high
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      RealPhysicalIdentification J lam corrH corrL → ∀ x : ℝ, 0 < x → realProduct lam x < 1 →
      Summable (corrH x) ∧
      highNormalizedBulk lam (x : ℂ) = (highCovarianceSum corrH x : ℂ) ∧
      highPhysicalBulk J lam (x : ℂ) = (highEnergyFieldResponse J corrH x : ℂ)))
  c03CheckType `IsingBulk.Anisotropic.RealPhysicalIdentification.low
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      RealPhysicalIdentification J lam corrH corrL → ∀ x : ℝ, 0 < x → 1 < realProduct lam x →
      Summable (fun v : LatticeSite => corrL x v - realMagnetizationSq lam x) ∧
      lowNormalizedBulk lam (x : ℂ) = (lowCovarianceSum lam corrL x : ℂ) ∧
      lowPhysicalBulk J lam (x : ℂ) = (lowEnergyFieldResponse J lam corrL x : ℂ)))
  c03CheckFields `IsingBulk.Anisotropic.RealUniformFieldIdentification
    #[`high_derivative, `high_zero, `low_derivative, `low_zero_square, `low_plus_positive]
  c03CheckType `IsingBulk.Anisotropic.RealUniformFieldIdentification.high_derivative
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      RealUniformFieldIdentification J lam corrH corrL mH mL → ∀ x,
      0 < x → realProduct lam x < 1 → HasDerivAt (mH x) (highEnergyFieldResponse J corrH x) 0))
  c03CheckType `IsingBulk.Anisotropic.RealUniformFieldIdentification.high_zero
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      RealUniformFieldIdentification J lam corrH corrL mH mL → ∀ x,
      0 < x → realProduct lam x < 1 → mH x 0 = 0))
  c03CheckType `IsingBulk.Anisotropic.RealUniformFieldIdentification.low_derivative
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      RealUniformFieldIdentification J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x →
      HasDerivWithinAt (mL x) (lowEnergyFieldResponse J lam corrL x) (Ioi 0) 0))
  c03CheckType `IsingBulk.Anisotropic.RealUniformFieldIdentification.low_zero_square
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      RealUniformFieldIdentification J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x → (mL x 0)^2 = realMagnetizationSq lam x))
  c03CheckType `IsingBulk.Anisotropic.RealUniformFieldIdentification.low_plus_positive
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      RealUniformFieldIdentification J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x → 0 < mL x 0))

run_cmd do
  c03CheckFields `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors
    #[`high_onsite, `low_onsite, `high_spin, `low_spin]
  c03CheckType `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors.high_onsite
    (← `(∀ {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL → ∀ x,
      0 < x → realProduct lam x < 1 → corrH x (0, 0) = 1))
  c03CheckType `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors.low_onsite
    (← `(∀ {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL → ∀ x,
      0 < x → 1 < realProduct lam x → corrL x (0, 0) = 1))
  c03CheckType `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors.high_spin
    (← `(∀ {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL → ∀ x,
      0 < x → realProduct lam x < 1 → ∀ v : LatticeSite,
      (corrH x v : ℂ) = (realHighPrefactor lam x : ℂ) * oddSiteSeries lam x v))
  c03CheckType `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors.low_spin
    (← `(∀ {lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ},
      PublishedRealSpinFormFactors lam corrH corrL → ∀ x,
      0 < x → 1 < realProduct lam x → ∀ v : LatticeSite,
      (corrL x v : ℂ) = (realMagnetizationSq lam x : ℂ) * (1 + evenSiteSeries lam x v)))
  c03CheckFields `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields
    #[`high, `low, `high_spin_flip, `low_zero_square, `low_plus_positive]
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields.high
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealGibbsFields J lam corrH corrL mH mL → ∀ x,
      0 < x → realProduct lam x < 1 → Nonempty (GibbsFieldConditions (x/(2*J)) (corrH x) (mH x))))
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields.low
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealGibbsFields J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x →
      Nonempty (GibbsFieldConditions (x/(2*J))
        (fun v : LatticeSite => corrL x v - realMagnetizationSq lam x) (mL x))))
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields.high_spin_flip
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealGibbsFields J lam corrH corrL mH mL → ∀ x,
      0 < x → realProduct lam x < 1 → ∀ h, mH x (-h) = -mH x h))
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields.low_zero_square
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealGibbsFields J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x → (mL x 0)^2 = realMagnetizationSq lam x))
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields.low_plus_positive
    (← `(∀ {J lam : ℝ} {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ},
      PublishedRealGibbsFields J lam corrH corrL mH mL → ∀ x,
      0 < x → 1 < realProduct lam x → 0 < mL x 0))
  c03CheckFields `IsingBulk.Anisotropic.PhysicalField.GibbsFieldConditions
    #[`enumeration, `localLaw, `volumeLaw, `local_center, `local_covariance,
      `field_monotonicity, `covariance_nonnegative, `pinned_covariance, `ghs_concavity,
      `thermodynamic_limit]
  c03CheckFields `IsingBulk.Anisotropic.PhysicalField.FiniteSpinLaw #[`weight, `nonneg, `normalized]
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.GibbsFieldConditions.mk
    (← `(∀ {β : ℝ} {c : LatticeSite → ℝ} {m : ℝ → ℝ}
      (enumeration : ℕ ≃ LatticeSite) (localLaw volumeLaw : ∀ n : ℕ, FiniteSpinLaw n),
      (∀ n, (localLaw n).centerMean = m 0) →
      (∀ n (i : Fin n), (localLaw n).siteCovariance i = c (enumeration i.val)) →
      (∀ n h, 0 < h → (localLaw n).magnetization β h ≤ m h) →
      (∀ v : LatticeSite, 0 ≤ c v) →
      (∀ n (i : Fin n), (volumeLaw n).siteCovariance i ≤ c (enumeration i.val)) →
      (∀ n, ConcaveOn ℝ (Ici 0) ((volumeLaw n).magnetization β)) →
      (∀ h, 0 ≤ h → Tendsto (fun n => (volumeLaw n).magnetization β h) atTop (𝓝 (m h))) →
      GibbsFieldConditions β c m))
  c03CheckType `IsingBulk.Anisotropic.PhysicalField.FiniteSpinLaw.mk
    (← `(∀ {n : ℕ} (weight : SpinConfig n → ℝ),
      (∀ ω, 0 ≤ weight ω) → (∑ ω, weight ω = 1) → FiniteSpinLaw n))
  logInfo "F002_FINAL_ORIGINAL_FIELDS_AND_PHYSICAL_SCOPE_PASS"

/-- Both original positive-real phase gates are inhabited for every admissible
ratio. This checks that the phase-indexed conclusions are not empty restrictions. -/
theorem c03_original_real_phase_gates_nonempty {lam : ℝ} (hlam : 0 < lam) :
    (∃ x : ℝ, 0 < x ∧ realProduct lam x < 1) ∧
      (∃ x : ℝ, 0 < x ∧ 1 < realProduct lam x) := by
  have hc := Geometry.criticalPointF002_pos hlam
  constructor
  · refine ⟨Geometry.criticalPointF002 lam / 2, by positivity, ?_⟩
    apply (Physical.realProduct_lt_one_iff_lt_critical hlam (by positivity)).mpr
    linarith
  · refine ⟨Geometry.criticalPointF002 lam + 1, by positivity, ?_⟩
    apply (Physical.critical_lt_iff_realProduct_gt_one hlam (by positivity)).mp
    linarith

end IsingBulk.AnisoF002.Audit
