import IsingBulk.AnisoF002.Isotropic.CovarianceField
import Mathlib.Analysis.Complex.Basic

/-!
# F002: coercivity on the actual balanced contour

The variance in F002 is complex bilinear, not Hermitian.  Positivity is
proved only for `U i = θ i - I*h i` with controlled real shifts.  The
protected-neighborhood lemma is a quantitative perturbation statement,
not a positivity assertion for unrestricted complex tuples.
-/
noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Real unordered-pair energy, in a symmetric double-sum representation. -/
def realPairEnergy (θ : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, (θ i - θ j) ^ 2

theorem realPairEnergy_nonneg (θ : ι → ℝ) : 0 ≤ realPairEnergy θ := by
  unfold realPairEnergy
  positivity

omit [Fintype ι] in
theorem contour_pair_square_re (θ h : ι → ℝ) (i j : ι) :
    ((contourCoordinate θ h i - contourCoordinate θ h j) ^ 2).re =
      (θ i - θ j) ^ 2 - (h i - h j) ^ 2 := by
  simp [contourCoordinate, pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- Exact cancellation of the imaginary cross terms after taking the real part. -/
theorem contour_variance_re (θ h : ι → ℝ) :
    (pairVariance (contourCoordinate θ h)).re =
      realPairEnergy θ - realPairEnergy h := by
  unfold pairVariance realPairEnergy
  norm_num [Complex.mul_re, Complex.re_sum, contour_pair_square_re,
    Finset.sum_sub_distrib]
  ring

/-- Uniform small Lipschitz shifts give coercivity of the bilinear variance. -/
theorem contour_variance_coercive (θ h : ι → ℝ) (c : ℝ)
    (hshift : ∀ i j, (h i - h j) ^ 2 ≤ c ^ 2 * (θ i - θ j) ^ 2) :
    (1 - c ^ 2) * realPairEnergy θ ≤
      (pairVariance (contourCoordinate θ h)).re := by
  have hb : realPairEnergy h ≤ c ^ 2 * realPairEnergy θ := by
    unfold realPairEnergy
    have hs : (∑ i, ∑ j, (h i - h j) ^ 2) ≤
        ∑ i, ∑ j, c ^ 2 * (θ i - θ j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => hshift i j
    simp only [← Finset.mul_sum] at hs
    nlinarith
  rw [contour_variance_re]
  nlinarith

/-- Nonzero angular diameter excludes the full equality locus. -/
theorem realPairEnergy_pos_of_ne (θ : ι → ℝ) (i j : ι) (hij : θ i ≠ θ j) :
    0 < realPairEnergy θ := by
  have hs : 0 < (θ i - θ j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hij)
  have h1 : (θ i - θ j) ^ 2 ≤ ∑ k, (θ i - θ k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (θ i - θ k)) (Finset.mem_univ j)
  have h2 : (∑ k, (θ i - θ k) ^ 2) ≤ ∑ l, ∑ k, (θ l - θ k) ^ 2 :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg (θ l - θ k))
      (Finset.mem_univ i)
  unfold realPairEnergy
  linarith

/-- Partial collisions are allowed: only full equality can make this denominator zero. -/
theorem contour_variance_ne_zero (θ h : ι → ℝ) (c : ℝ)
    (hc : c ^ 2 < 1)
    (hshift : ∀ i j, (h i - h j) ^ 2 ≤ c ^ 2 * (θ i - θ j) ^ 2)
    (i j : ι) (hij : θ i ≠ θ j) :
    pairVariance (contourCoordinate θ h) ≠ 0 := by
  have hp := realPairEnergy_pos_of_ne θ i j hij
  have hb := contour_variance_coercive θ h c hshift
  have hpos : 0 < (pairVariance (contourCoordinate θ h)).re :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr hc) hp) hb
  intro hz
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos

/-- A protected complex perturbation preserves half the actual positive real part. -/
theorem protected_variance_re (D D' : ℂ)
    (h : ‖D' - D‖ ≤ D.re / 2) : D.re / 2 ≤ D'.re := by
  have hr := Complex.abs_re_le_norm (D' - D)
  have hl : -(D' - D).re ≤ |(D' - D).re| := neg_le_abs _
  simp only [Complex.sub_re] at hr hl
  linarith

theorem protected_variance_ne_zero (D D' : ℂ) (hD : 0 < D.re)
    (h : ‖D' - D‖ ≤ D.re / 2) : D' ≠ 0 := by
  have hp := protected_variance_re D D' h
  intro hz
  rw [hz] at hp
  norm_num at hp
  linarith

end IsingBulk.AnisoF002.Isotropic
