import IsingBulk.AnisoF002.C03.IsotropicOneSidedInverse

/-!
# A nonvanishing complete-pair quotient on the whole one-sided arc

The physical boundary phase has real part arccos(x) also on x>1,
where that real part is zero. Its cosine is real. The divided cosine
identity then proves a nonnegative real part of the phase secant;
the actual angular secant is strictly negative off the diagonal.
This supplies the global collision coefficient without local patching.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric Filter

theorem upperBoundaryPhase_re_arccos (x : ℝ) (hx : -1 < x) :
    (upperBoundaryPhase x).re = Real.arccos x := by
  by_cases hx1 : x ≤ 1
  · rw [upperBoundaryPhase_eq_arccos x hx hx1, Complex.ofReal_re]
  · rw [upperBoundaryPhase_re_zero x (le_of_not_ge hx1),
      Real.arccos_eq_zero.mpr (le_of_not_ge hx1)]

theorem real_divided_cosine_nonneg (a b : ℂ) (x y : ℝ)
    (ha : Complex.cos a = (x : ℂ)) (hb : Complex.cos b = (y : ℂ))
    (hre : 0 ≤ (y - x) * (a.re - b.re))
    (hdiag : a = b → 0 ≤ (Complex.sin a).re) :
    0 ≤ (minusCosineSecant a b).re := by
  by_cases hab : a = b
  · rw [hab, minusCosineSecant_self]
    simpa only [hab] using hdiag hab
  · let d := a - b
    let B := minusCosineSecant a b
    have hd : d ≠ 0 := sub_ne_zero.mpr hab
    have hpos : 0 < d.re ^ 2 + d.im ^ 2 := by
      have hh : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
      rw [Complex.sq_norm, Complex.normSq_apply] at hh
      nlinarith
    have he : d * B = ((y - x : ℝ) : ℂ) := by
      have h := minusCosineSecant_difference a b
      rw [ha, hb] at h
      dsimp only [d, B]
      push_cast
      linear_combination -h
    have her := congrArg Complex.re he
    have hei := congrArg Complex.im he
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at her hei
    have hid : (d.re ^ 2 + d.im ^ 2) * B.re = (y - x) * d.re := by
      linear_combination d.re * her + d.im * hei
    have hnonneg : 0 ≤ (d.re ^ 2 + d.im ^ 2) * B.re := by
      rw [hid]
      simpa only [d, Complex.sub_re] using hre
    change 0 ≤ B.re
    nlinarith

/-- Actual phase secants across the right/left join have nonnegative
real part, including the branch and every coincident pair. -/
theorem upperBoundaryPhase_secant_re_nonneg (x y : ℝ) (hx : -1 < x) (hy : -1 < y) :
    0 ≤ (minusCosineSecant (upperBoundaryPhase x) (upperBoundaryPhase y)).re := by
  apply real_divided_cosine_nonneg _ _ x y
    (upperBoundaryPhase_cos x hx) (upperBoundaryPhase_cos y hy)
  · rw [upperBoundaryPhase_re_arccos x hx, upperBoundaryPhase_re_arccos y hy]
    rcases le_total x y with h | h
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.arccos_le_arccos h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (Real.arccos_le_arccos h))
  · intro _
    have hr := upperBoundaryPhase_re_range x hx
    rw [Complex.sin_eq]
    simpa [Complex.sin_ofReal_re] using
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.1 hr.2.le)
        (Real.cosh_pos (upperBoundaryPhase x).im).le

theorem angular_secant_re_neg (wa wb : ℝ)
    (ha : wa ∈ Icc (-Real.pi) 0) (hb : wb ∈ Icc (-Real.pi) 0) (hab : wa ≠ wb) :
    (minusCosineSecant (wa : ℂ) (wb : ℂ)).re < 0 := by
  rw [minusCosineSecant_ofReal, Complex.ofReal_re]
  have hsum0 : wa + wb < 0 := by
    by_contra hn
    have he : wa = wb := by linarith [ha.2, hb.2]
    exact hab he
  have hsumpi : -2 * Real.pi < wa + wb := by
    by_contra hn
    have he : wa = wb := by linarith [ha.1, hb.1]
    exact hab he
  apply mul_neg_of_neg_of_pos
  · apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith
  · apply realSincF002_pos
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, Real.pi_pos]

theorem inverseSecantDenominator_oneSided_ne_zero (S wa wb : ℝ)
    (hS : 0 < S ∧ S < 2)
    (ha : wa ∈ Icc (-Real.pi) 0) (hb : wb ∈ Icc (-Real.pi) 0) :
    inverseSecantDenominator explicitRightInverse
      ((S : ℂ), oneSidedBoundaryCoordinate S wa, oneSidedBoundaryCoordinate S wb) ≠ 0 := by
  have hUa := explicitRightInverse_on_oneSided_arc S wa hS ha
  have hUb := explicitRightInverse_on_oneSided_arc S wb hS hb
  by_cases hab : wa = wb
  · subst wb
    simpa only [inverseSecantDenominator, minusCosineSecant_self, explicitRightDenominator]
      using hUa.2.2.2
  · have hxa : -1 < S - Real.cos wa := by linarith [hS.1, Real.cos_le_one wa]
    have hxb : -1 < S - Real.cos wb := by linarith [hS.1, Real.cos_le_one wb]
    have hphase := upperBoundaryPhase_secant_re_nonneg
      (S - Real.cos wa) (S - Real.cos wb) hxa hxb
    have hangle := angular_secant_re_neg wa wb ha hb hab
    have hpa : oneSidedBoundaryCoordinate S wa - (wa : ℂ) =
        upperBoundaryPhase (S - Real.cos wa) := by dsimp [oneSidedBoundaryCoordinate]; ring
    have hpb : oneSidedBoundaryCoordinate S wb - (wb : ℂ) =
        upperBoundaryPhase (S - Real.cos wb) := by dsimp [oneSidedBoundaryCoordinate]; ring
    apply ne_of_apply_ne Complex.re
    apply ne_of_gt
    simp only [inverseSecantDenominator, hUa.1, hUb.1, hpa, hpb, Complex.sub_re, Complex.zero_re]
    linarith

def oneSidedCoordinateArc (S : ℝ) : Set ℂ := oneSidedBoundaryCoordinate S '' Icc (-Real.pi) 0

def oneSidedParameterArc (S : ℝ) : Set (ℂ × ℂ) := {(S : ℂ)} ×ˢ oneSidedCoordinateArc S

def oneSidedPairParameterArc (S : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {(S : ℂ)} ×ˢ (oneSidedCoordinateArc S ×ˢ oneSidedCoordinateArc S)

theorem oneSidedCoordinateArc_isCompact (S : ℝ) (hS : 0 < S) :
    IsCompact (oneSidedCoordinateArc S) :=
  isCompact_Icc.image (oneSidedBoundaryCoordinate_continuous S hS)

theorem oneSidedParameterArc_isCompact (S : ℝ) (hS : 0 < S) :
    IsCompact (oneSidedParameterArc S) :=
  isCompact_singleton.prod (oneSidedCoordinateArc_isCompact S hS)

theorem oneSidedPairParameterArc_isCompact (S : ℝ) (hS : 0 < S) :
    IsCompact (oneSidedPairParameterArc S) :=
  isCompact_singleton.prod ((oneSidedCoordinateArc_isCompact S hS).prod
    (oneSidedCoordinateArc_isCompact S hS))

theorem explicitRightInverse_data_on_oneSided_arc (S : ℝ) (hS : 0 < S ∧ S < 2)
    (q : ℂ × ℂ) (hq : q ∈ oneSidedParameterArc S) :
    AnalyticAt ℂ explicitRightInverse q ∧ Complex.cos (q.2 / 2) ≠ 0 ∧
      explicitRightDenominator q ≠ 0 := by
  rcases q with ⟨s, v⟩
  rcases hq with ⟨hs, w, hw, hv⟩
  change s = (S : ℂ) at hs
  subst s
  change oneSidedBoundaryCoordinate S w = v at hv
  subst v
  exact (explicitRightInverse_on_oneSided_arc S w hS hw).2

theorem oneSidedPairParameterArc_fst_mem {S : ℝ} {q : ℂ × ℂ × ℂ}
    (hq : q ∈ oneSidedPairParameterArc S) : (q.1, q.2.1) ∈ oneSidedParameterArc S :=
  ⟨hq.1, hq.2.1⟩

theorem oneSidedPairParameterArc_snd_mem {S : ℝ} {q : ℂ × ℂ × ℂ}
    (hq : q ∈ oneSidedPairParameterArc S) : (q.1, q.2.2) ∈ oneSidedParameterArc S :=
  ⟨hq.1, hq.2.2⟩

theorem inverseSecantDenominator_oneSidedPair_ne_zero (S : ℝ) (hS : 0 < S ∧ S < 2)
    (q : ℂ × ℂ × ℂ) (hq : q ∈ oneSidedPairParameterArc S) :
    inverseSecantDenominator explicitRightInverse q ≠ 0 := by
  rcases q with ⟨s, a, b⟩
  rcases hq with ⟨hs, ⟨wa, hwa, hca⟩, ⟨wb, hwb, hcb⟩⟩
  change s = (S : ℂ) at hs
  subst s
  change oneSidedBoundaryCoordinate S wa = a at hca
  change oneSidedBoundaryCoordinate S wb = b at hcb
  subst a
  subst b
  exact inverseSecantDenominator_oneSided_ne_zero S wa wb hS hwa hwb

end IsingBulk.AnisoF002.Isotropic
