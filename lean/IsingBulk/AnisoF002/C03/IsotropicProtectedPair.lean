import IsingBulk.AnisoF002.C03.IsotropicCollisionPair

/-!
# Protected collision coefficient on the whole actual right arc

The single coefficient of `IsotropicCollisionPair` is regular on the
entire right pair interval. Compactness supplies one complex neighborhood
with every fixed joint jet bounded, before the particle number is chosen.
This proves the right-arc part of frozen `eq:iso-pair-zero`.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set Metric

def realSincF002 (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

theorem complexSinc_ofReal (x : ℝ) : complexSinc (x : ℂ) = (realSincF002 x : ℂ) := by
  by_cases hx : x = 0
  · simp [hx, realSincF002]
  · simp only [complexSinc, dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx),
      slope_def_field, Complex.sin_zero, sub_zero, realSincF002, ite_eq_right hx,
      Complex.ofReal_div, Complex.ofReal_sin]

theorem realSincF002_pos {x : ℝ} (hx : -Real.pi < x ∧ x < Real.pi) :
    0 < realSincF002 x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [realSincF002, ite_eq_right h.ne]
    exact div_pos_of_neg_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h hx.1) h
  · norm_num [realSincF002]
  · rw [realSincF002, ite_eq_right h.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi h hx.2) h

theorem minusCosineSecant_ofReal (a b : ℝ) :
    minusCosineSecant (a : ℂ) (b : ℂ) =
      (Real.sin ((a + b) / 2) * realSincF002 ((a - b) / 2) : ℝ) := by
  have hs : ((a : ℂ) + (b : ℂ)) / 2 = (((a + b) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hd : ((a : ℂ) - (b : ℂ)) / 2 = (((a - b) / 2 : ℝ) : ℂ) := by push_cast; rfl
  unfold minusCosineSecant
  rw [hs, hd, complexSinc_ofReal]
  push_cast
  rfl

/-- Strict positivity of the new quotient denominator is proved on the
actual whole right arc; it is not an extra physical hypothesis. -/
theorem inverseSecantDenominator_real_right_pos (S wa wb : ℝ)
    (hS : 0 < S ∧ S < 2)
    (hwa : wa ∈ Icc (-rightBranchEndpoint S) 0)
    (hwb : wb ∈ Icc (-rightBranchEndpoint S) 0) :
    0 < (inverseSecantDenominator explicitRightInverse
      ((S : ℂ), (rightArcCoordinate S wa : ℂ), (rightArcCoordinate S wb : ℂ))).re := by
  have ha := explicitRightInverse_on_right_arc S wa hS hwa
  have hb := explicitRightInverse_on_right_arc S wb hS hwb
  have hφa : (rightArcCoordinate S wa : ℂ) - (wa : ℂ) = (rightArcPhase S wa : ℂ) := by
    simp [rightArcCoordinate]
  have hφb : (rightArcCoordinate S wb : ℂ) - (wb : ℂ) = (rightArcPhase S wb : ℂ) := by
    simp [rightArcCoordinate]
  simp only [inverseSecantDenominator, ha, hb, hφa, hφb, minusCosineSecant_ofReal,
    ← Complex.ofReal_sub, Complex.ofReal_re]
  have hpa := rightArcPhase_range S wa hS.1
  have hpb := rightArcPhase_range S wb hS.1
  have hbpi := rightBranchEndpoint_lt_pi S hS.1
  have hwSinc : 0 < realSincF002 ((wa - wb) / 2) := by
    apply realSincF002_pos
    constructor <;> linarith [hwa.1, hwa.2, hwb.1, hwb.2, Real.pi_pos]
  have hpSinc : 0 < realSincF002 ((rightArcPhase S wa - rightArcPhase S wb) / 2) := by
    apply realSincF002_pos
    constructor <;> linarith [hpa.1, hpa.2, hpb.1, hpb.2, Real.pi_pos]
  have hpSin : 0 ≤ Real.sin ((rightArcPhase S wa + rightArcPhase S wb) / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hpa.1, hpa.2, hpb.1, hpb.2]
  by_cases hz : wa = 0 ∧ wb = 0
  · rcases hz with ⟨rfl, rfl⟩
    have hpos := rightArc_inverse_denominator_pos S 0 hS hwa
    simp only [Real.sin_zero, sub_zero] at hpos
    simpa [show (rightArcPhase S 0 + rightArcPhase S 0) / 2 = rightArcPhase S 0 by ring,
      realSincF002] using hpos
  · have hsum : wa + wb < 0 := by
      by_contra h
      push Not at h
      have hwa0 : wa = 0 := by linarith [hwa.2, hwb.2]
      have hwb0 : wb = 0 := by linarith [hwa.2, hwb.2]
      exact hz ⟨hwa0, hwb0⟩
    have hneg : Real.sin ((wa + wb) / 2) < 0 := by
      apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith [hwa.1, hwb.1]
    have hleft := mul_nonneg hpSin hpSinc.le
    have hright := mul_neg_of_neg_of_pos hneg hwSinc
    linarith

theorem inverseSecantDenominator_rightPair_ne_zero (S : ℝ) (hS : 0 < S ∧ S < 2)
    (q : ℂ × ℂ × ℂ) (hq : q ∈ rightPairParameterSegment S) :
    inverseSecantDenominator explicitRightInverse q ≠ 0 := by
  rcases q with ⟨s, a, b⟩
  rcases hq with ⟨hs, ⟨ar, har, hca⟩, ⟨br, hbr, hcb⟩⟩
  change s = (S : ℂ) at hs
  subst s
  change (ar : ℂ) = a at hca
  change (br : ℂ) = b at hcb
  subst a
  subst b
  rw [← rightArcCoordinate_image S hS] at har hbr
  rcases har with ⟨wa, hwa, rfl⟩
  rcases hbr with ⟨wb, hwb, rfl⟩
  intro hz
  have hp := inverseSecantDenominator_real_right_pos S wa wb hS hwa hwb
  rw [hz, Complex.zero_re] at hp
  exact lt_irrefl _ hp

/-- One common complex neighborhood carries the complete pair and its
literal retained collision coefficient. Every fixed joint jet is bounded
on the same protected closed set. -/
theorem exists_right_completePair_protected_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r : ℝ, 0 < r ∧
      rightPairParameterSegment S ⊆ thickening r (rightPairParameterSegment S) ∧
      AnalyticOnNhd ℂ (inversePairFilled explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      AnalyticOnNhd ℂ (inversePairCollisionCoefficient explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S),
        inversePairFilled explicitRightInverse q =
          (q.2.1 - q.2.2) ^ 2 * inversePairCollisionCoefficient explicitRightInverse q) ∧
      ∀ k : ℕ, ∃ C₁ C₂ : ℝ,
        (∀ q ∈ cthickening r (rightPairParameterSegment S),
          ‖iteratedFDeriv ℂ k (inversePairFilled explicitRightInverse) q‖ ≤ C₁) ∧
        (∀ q ∈ cthickening r (rightPairParameterSegment S),
          ‖iteratedFDeriv ℂ k (inversePairCollisionCoefficient explicitRightInverse) q‖ ≤ C₂) := by
  let P : (ℂ × ℂ × ℂ) → Prop := fun q =>
    AnalyticAt ℂ explicitRightInverse (q.1, q.2.1) ∧
      AnalyticAt ℂ explicitRightInverse (q.1, q.2.2) ∧
      Complex.cos (q.2.1 / 2) ≠ 0 ∧ Complex.cos (q.2.2 / 2) ≠ 0 ∧
      inverseSecantDenominator explicitRightInverse q ≠ 0
  have hinside : rightPairParameterSegment S ⊆ interior {q | P q} := by
    intro q hq
    apply mem_interior_iff_mem_nhds.mpr
    have ha := explicitRightInverse_data_on_segment S hS _ (rightPairParameterSegment_fst_mem hq)
    have hb := explicitRightInverse_data_on_segment S hS _ (rightPairParameterSegment_snd_mem hq)
    have hca : ContinuousAt (fun p : ℂ × ℂ × ℂ => Complex.cos (p.2.1 / 2)) q := by fun_prop
    have hcb : ContinuousAt (fun p : ℂ × ℂ × ℂ => Complex.cos (p.2.2 / 2)) q := by fun_prop
    have hma : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) q := by fun_prop
    have hmb : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) q := by fun_prop
    have hK := (inverseSecantDenominator_analyticAt explicitRightInverse q ha.1 hb.1).continuousAt
    filter_upwards [hma.eventually ha.1.eventually_analyticAt, hmb.eventually hb.1.eventually_analyticAt,
      hca.eventually_ne ha.2.1, hcb.eventually_ne hb.2.1,
      hK.eventually_ne (inverseSecantDenominator_rightPair_ne_zero S hS q hq)] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨r, hr, hsub⟩ := (rightPairParameterSegment_isCompact S).exists_cthickening_subset_open
    isOpen_interior hinside
  have hall : ∀ q ∈ cthickening r (rightPairParameterSegment S), P q :=
    fun q hq => (interior_subset (s := {q | P q})) (hsub hq)
  have hpair : AnalyticOnNhd ℂ (inversePairFilled explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) := by
    intro q hq
    have h := hall q hq
    exact inversePairFilled_analyticAt explicitRightInverse q h.1 h.2.1
      (explicitRightInverse_dispersion_eventually _ h.2.2.1)
      (explicitRightInverse_dispersion_eventually _ h.2.2.2.1) h.2.2.2.2
  have hcoeff : AnalyticOnNhd ℂ (inversePairCollisionCoefficient explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) := by
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
    obtain ⟨C₁, h₁⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
      (hpair.iteratedFDeriv k).continuousOn
    obtain ⟨C₂, h₂⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
      (hcoeff.iteratedFDeriv k).continuousOn
    exact ⟨C₁, C₂, h₁, h₂⟩

end IsingBulk.AnisoF002.Isotropic
