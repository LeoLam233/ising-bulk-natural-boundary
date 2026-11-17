import IsingBulk.AnisoF002.Isotropic.RightNeighborhood
import IsingBulk.AnisoF002.Isotropic.CovarianceField
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual filled analytic secants and covariance constraints

The secants here are formed from the actual function and its actual
derivative, including their diagonal values.  The fundamental theorem of
calculus supplies their segment-integral representation.  Positive real
curvature on the common convex neighborhood therefore proves nonvanishing
of every second secant, also at a partial coincidence.

This constructs the scalar secant mechanism in frozen F002 (7.32) and
connects it to the earlier checked covariance algebra.  Joint analyticity
of all filled secants, protected all-angular jets, and physical coarea
integration remain separate obligations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set MeasureTheory Metric

def complexSegmentPath (a b : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * (b - a)

theorem complexSegmentPath_mem {D : Set ℂ} (hD : Convex ℝ D)
    {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) {t : ℝ} (ht : t ∈ Icc 0 1) :
    complexSegmentPath a b t ∈ D := by
  simpa only [complexSegmentPath, Complex.real_smul] using hD.add_smul_sub_mem ha hb ht

theorem complexSegmentPath_continuous (a b : ℂ) : Continuous (complexSegmentPath a b) := by
  unfold complexSegmentPath
  fun_prop

theorem complexSegmentPath_hasDerivAt (a b : ℂ) (t : ℝ) :
    HasDerivAt (complexSegmentPath a b) (b - a) t := by
  simpa only [complexSegmentPath, id_eq, Complex.ofReal_one, one_mul] using!
    (((hasDerivAt_id t).ofReal_comp).mul_const (b - a)).const_add a

@[simp] theorem complexSegmentPath_zero (a b : ℂ) : complexSegmentPath a b 0 = a := by
  simp [complexSegmentPath]

@[simp] theorem complexSegmentPath_one (a b : ℂ) : complexSegmentPath a b 1 = b := by
  simp [complexSegmentPath]

theorem analytic_comp_segment_intervalIntegrable (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) {a b : ℂ}
    (ha : a ∈ D) (hb : b ∈ D) :
    IntervalIntegrable (fun t => f (complexSegmentPath a b t)) volume 0 1 := by
  exact (hf.continuousOn.comp (complexSegmentPath_continuous a b).continuousOn
    (fun t ht => complexSegmentPath_mem hD ha hb ht)).intervalIntegrable_of_Icc (by norm_num)

/-- The genuine filled derivative secant equals its line integral,
including when the two arguments coincide. -/
theorem dslope_eq_segment_integral (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) {a b : ℂ}
    (ha : a ∈ D) (hb : b ∈ D) :
    dslope f a b = ∫ t in (0 : ℝ)..1, deriv f (complexSegmentPath a b t) := by
  by_cases hab : b = a
  · subst b
    simp [complexSegmentPath]
  · have hint := analytic_comp_segment_intervalIntegrable (deriv f) hD hf.deriv ha hb
    have hpath : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t => f (complexSegmentPath a b t))
          (deriv f (complexSegmentPath a b t) * (b - a)) t := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hft := (hf _ (complexSegmentPath_mem hD ha hb ht')).differentiableAt.hasDerivAt
      simpa only [Function.comp_apply] using! hft.comp t (complexSegmentPath_hasDerivAt a b t)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath (hint.mul_const (b - a))
    have heq : (∫ t in (0 : ℝ)..1, deriv f (complexSegmentPath a b t)) * (b - a) =
        f b - f a := by
      simpa only [intervalIntegral.integral_mul_const, complexSegmentPath_one,
        complexSegmentPath_zero] using hFTC
    apply mul_right_cancel₀ (sub_ne_zero.mpr hab)
    calc
      dslope f a b * (b - a) = (b - a) * dslope f a b := mul_comm _ _
      _ = f b - f a := by simpa only [smul_eq_mul] using sub_smul_dslope f a b
      _ = (∫ t in (0 : ℝ)..1, deriv f (complexSegmentPath a b t)) * (b - a) := heq.symm

theorem complex_dslope_symmetric (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases hab : a = b
  · subst b
    rfl
  · rw [dslope_of_ne _ (Ne.symm hab), dslope_of_ne _ hab]
    exact slope_comm f a b

/-- Positive curvature passes to every actual filled second secant by
integration over a segment of the common convex domain. -/
theorem second_secant_re_lower_bound (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) (c : ℝ)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (deriv f) z).re)
    {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) :
    c ≤ (dslope (deriv f) a b).re := by
  rw [dslope_eq_segment_integral (deriv f) hD hf.deriv ha hb]
  have hint := analytic_comp_segment_intervalIntegrable (deriv (deriv f)) hD hf.deriv.deriv ha hb
  have hintr : IntervalIntegrable
      (fun t => (deriv (deriv f) (complexSegmentPath a b t)).re) volume 0 1 :=
    ⟨hint.1.re, hint.2.re⟩
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := c)) hintr
    (fun t ht => hcurv _ (complexSegmentPath_mem hD ha hb ht))
  have hre : (∫ t in (0 : ℝ)..1, (deriv (deriv f) (complexSegmentPath a b t)).re) =
      (∫ t in (0 : ℝ)..1, deriv (deriv f) (complexSegmentPath a b t)).re :=
    intervalIntegral.intervalIntegral_re hint
  rw [hre] at hm
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hm

theorem second_secant_ne_zero (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) (c : ℝ) (hc : 0 < c)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (deriv f) z).re)
    {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) :
    dslope (deriv f) a b ≠ 0 := by
  intro hz
  have h := second_secant_re_lower_bound f hD hf c hcurv ha hb
  rw [hz, Complex.zero_re] at h
  linarith

variable {ι : Type*} [Fintype ι]

/-- Filled pair kernel made from the actual first and second secants. -/
def analyticSecantPair (f : ℂ → ℂ) (v : ι → ℂ) (i j : ι) : ℂ :=
  secantPair v (fun i j => dslope f (v j) (v i))
    (fun i j => dslope (deriv f) (v j) (v i)) i j

def analyticCovarianceField (A : ℂ) (f : ℂ → ℂ) (v : ι → ℂ) (i : ι) : ℂ :=
  covarianceField A (fun j => f (v j)) (analyticSecantPair f v) i

omit [Fintype ι] in
theorem analyticSecantPair_antisymm (f : ℂ → ℂ) (v : ι → ℂ) (i j : ι) :
    analyticSecantPair f v j i = -analyticSecantPair f v i j := by
  apply secantPair_antisymm
  · intro i j
    exact complex_dslope_symmetric f (v i) (v j)
  · intro i j
    exact complex_dslope_symmetric (deriv f) (v i) (v j)

omit [Fintype ι] in
theorem analyticSecantPair_contract (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) (c : ℝ) (hc : 0 < c)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (deriv f) z).re)
    (v : ι → ℂ) (hv : ∀ i, v i ∈ D) (i j : ι) :
    (deriv f (v i) - deriv f (v j)) * analyticSecantPair f v i j =
      (f (v i) - f (v j)) ^ 2 := by
  apply secantPair_contract v (fun i => f (v i)) (fun i => deriv f (v i))
    (fun i j => dslope f (v j) (v i)) (fun i j => dslope (deriv f) (v j) (v i))
  · intro i j
    simpa only [smul_eq_mul] using (sub_smul_dslope f (v j) (v i)).symm
  · intro i j
    simpa only [smul_eq_mul] using (sub_smul_dslope (deriv f) (v j) (v i)).symm
  · intro i j
    exact second_secant_ne_zero f hD hf c hc hcurv (hv j) (hv i)

theorem analyticCovarianceField_sum (A : ℂ) (f : ℂ → ℂ) (v : ι → ℂ) :
    ∑ i, analyticCovarianceField A f v i = 0 :=
  covarianceField_sum A (fun j => f (v j)) (analyticSecantPair f v)
    (analyticSecantPair_antisymm f v)

theorem analyticCovarianceField_weighted (A : ℂ) (f : ℂ → ℂ) {D : Set ℂ}
    (hD : Convex ℝ D) (hf : AnalyticOnNhd ℂ f D) (c : ℝ) (hc : 0 < c)
    (hcurv : ∀ z ∈ D, c ≤ (deriv (deriv f) z).re)
    (v : ι → ℂ) (hv : ∀ i, v i ∈ D) (hvar : pairVariance (fun i => f (v i)) ≠ 0) :
    (∑ i, deriv f (v i) * analyticCovarianceField A f v i) = A :=
  covarianceField_weighted A (fun i => f (v i)) (fun i => deriv f (v i))
    (analyticSecantPair f v) (analyticSecantPair_antisymm f v)
    (analyticSecantPair_contract f hD hf c hc hcurv v hv) hvar

end IsingBulk.AnisoF002.Isotropic
