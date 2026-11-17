import IsingBulk.AnisoF002.C03.IsotropicOneSidedSecants

/-!
# Protected inverse and complete pair on the entire one-sided arc

The actual left/right boundary values have one common complex
neighborhood for the explicit inverse, its regular denominator,
the original complete pair, and the literal collision coefficient.
Every fixed joint jet is bounded on the same protected closed set.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set Metric

theorem exists_oneSided_inverse_protected_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ explicitRightInverse (cthickening r (oneSidedParameterArc S)) ∧
      (∀ q ∈ cthickening r (oneSidedParameterArc S),
        Complex.cos (explicitRightInverse q) +
            Complex.cos (q.2 - explicitRightInverse q) = q.1 ∧
          Complex.cos (q.2 / 2) ≠ 0 ∧ explicitRightDenominator q ≠ 0) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ q ∈ cthickening r (oneSidedParameterArc S),
        ‖iteratedFDeriv ℂ k explicitRightInverse q‖ ≤ C := by
  let P : (ℂ × ℂ) → Prop := fun q =>
    AnalyticAt ℂ explicitRightInverse q ∧ Complex.cos (q.2 / 2) ≠ 0 ∧
      explicitRightDenominator q ≠ 0
  have hinside : oneSidedParameterArc S ⊆ interior {q | P q} := by
    intro q hq
    apply mem_interior_iff_mem_nhds.mpr
    have hd := explicitRightInverse_data_on_oneSided_arc S hS q hq
    have hc : ContinuousAt (fun p : ℂ × ℂ => Complex.cos (p.2 / 2)) q := by fun_prop
    have hD := (explicitRightDenominator_analyticAt q hd.1).continuousAt
    filter_upwards [hd.1.eventually_analyticAt, hc.eventually_ne hd.2.1,
      hD.eventually_ne hd.2.2] with p hU hc hD
    exact ⟨hU, hc, hD⟩
  obtain ⟨r, hr, hsub⟩ := (oneSidedParameterArc_isCompact S hS.1).exists_cthickening_subset_open
    isOpen_interior hinside
  have hall : ∀ q ∈ cthickening r (oneSidedParameterArc S), P q :=
    fun q hq => (interior_subset (s := {q | P q})) (hsub hq)
  have hU : AnalyticOnNhd ℂ explicitRightInverse (cthickening r (oneSidedParameterArc S)) :=
    fun q hq => (hall q hq).1
  refine ⟨r, hr, hU, ?_, ?_⟩
  · intro q hq
    have h := hall q hq
    exact ⟨explicitRightInverse_dispersion q h.2.1, h.2⟩
  · intro k
    exact (oneSidedParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
      (hU.iteratedFDeriv k).continuousOn

/-- The literal collision factorization and every fixed pair/coefficient
jet hold on one common neighborhood of the whole arc squared. -/
theorem exists_oneSided_completePair_protected_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r : ℝ, 0 < r ∧
      oneSidedPairParameterArc S ⊆ thickening r (oneSidedPairParameterArc S) ∧
      AnalyticOnNhd ℂ (inversePairFilled explicitRightInverse)
        (cthickening r (oneSidedPairParameterArc S)) ∧
      AnalyticOnNhd ℂ (inversePairCollisionCoefficient explicitRightInverse)
        (cthickening r (oneSidedPairParameterArc S)) ∧
      (∀ q ∈ cthickening r (oneSidedPairParameterArc S),
        inversePairFilled explicitRightInverse q =
          (q.2.1 - q.2.2) ^ 2 * inversePairCollisionCoefficient explicitRightInverse q) ∧
      ∀ k : ℕ, ∃ C₁ C₂ : ℝ,
        (∀ q ∈ cthickening r (oneSidedPairParameterArc S),
          ‖iteratedFDeriv ℂ k (inversePairFilled explicitRightInverse) q‖ ≤ C₁) ∧
        (∀ q ∈ cthickening r (oneSidedPairParameterArc S),
          ‖iteratedFDeriv ℂ k (inversePairCollisionCoefficient explicitRightInverse) q‖ ≤ C₂) := by
  let P : (ℂ × ℂ × ℂ) → Prop := fun q =>
    AnalyticAt ℂ explicitRightInverse (q.1, q.2.1) ∧
      AnalyticAt ℂ explicitRightInverse (q.1, q.2.2) ∧
      Complex.cos (q.2.1 / 2) ≠ 0 ∧ Complex.cos (q.2.2 / 2) ≠ 0 ∧
      inverseSecantDenominator explicitRightInverse q ≠ 0
  have hinside : oneSidedPairParameterArc S ⊆ interior {q | P q} := by
    intro q hq
    apply mem_interior_iff_mem_nhds.mpr
    have ha := explicitRightInverse_data_on_oneSided_arc S hS _ (oneSidedPairParameterArc_fst_mem hq)
    have hb := explicitRightInverse_data_on_oneSided_arc S hS _ (oneSidedPairParameterArc_snd_mem hq)
    have hca : ContinuousAt (fun p : ℂ × ℂ × ℂ => Complex.cos (p.2.1 / 2)) q := by fun_prop
    have hcb : ContinuousAt (fun p : ℂ × ℂ × ℂ => Complex.cos (p.2.2 / 2)) q := by fun_prop
    have hma : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) q := by fun_prop
    have hmb : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) q := by fun_prop
    have hK := (inverseSecantDenominator_analyticAt explicitRightInverse q ha.1 hb.1).continuousAt
    filter_upwards [hma.eventually ha.1.eventually_analyticAt, hmb.eventually hb.1.eventually_analyticAt,
      hca.eventually_ne ha.2.1, hcb.eventually_ne hb.2.1,
      hK.eventually_ne (inverseSecantDenominator_oneSidedPair_ne_zero S hS q hq)] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨r, hr, hsub⟩ := (oneSidedPairParameterArc_isCompact S hS.1).exists_cthickening_subset_open
    isOpen_interior hinside
  have hall : ∀ q ∈ cthickening r (oneSidedPairParameterArc S), P q :=
    fun q hq => (interior_subset (s := {q | P q})) (hsub hq)
  have hpair : AnalyticOnNhd ℂ (inversePairFilled explicitRightInverse)
      (cthickening r (oneSidedPairParameterArc S)) := by
    intro q hq
    have h := hall q hq
    exact inversePairFilled_analyticAt explicitRightInverse q h.1 h.2.1
      (explicitRightInverse_dispersion_eventually _ h.2.2.1)
      (explicitRightInverse_dispersion_eventually _ h.2.2.2.1) h.2.2.2.2
  have hcoeff : AnalyticOnNhd ℂ (inversePairCollisionCoefficient explicitRightInverse)
      (cthickening r (oneSidedPairParameterArc S)) := by
    intro q hq
    have h := hall q hq
    exact inversePairCollisionCoefficient_analyticAt explicitRightInverse q h.1 h.2.1 h.2.2.2.2
  refine ⟨r, hr, self_subset_thickening hr _, hpair, hcoeff, ?_, ?_⟩
  · intro q hq
    have h := hall q hq
    exact inversePairFilled_factorization explicitRightInverse q
      (explicitRightInverse_dispersion _ h.2.2.1)
      (explicitRightInverse_dispersion _ h.2.2.2.1) h.2.2.2.2
  · intro k
    obtain ⟨C₁, h₁⟩ := (oneSidedPairParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
      (hpair.iteratedFDeriv k).continuousOn
    obtain ⟨C₂, h₂⟩ := (oneSidedPairParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
      (hcoeff.iteratedFDeriv k).continuousOn
    exact ⟨C₁, C₂, h₁, h₂⟩

end IsingBulk.AnisoF002.Isotropic
