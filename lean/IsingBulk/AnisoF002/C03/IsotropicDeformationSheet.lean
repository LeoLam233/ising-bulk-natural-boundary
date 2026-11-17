import IsingBulk.AnisoF002.C03.RegularEdgeRoot
import IsingBulk.AnisoF002.Isotropic.BalancedLipschitz
import IsingBulk.AnisoF002.RegularTail.PhysicalFactors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The actual balanced homotopy stays on the interior spectral sheet

The global bump populations are kept in the contour. Their exact signs
preserve the upper half-plane dispersion throughout the homotopy, so
the actual unique interior root, all one-body and complete-pair
denominators, and the signed product denominator remain nonzero.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.Geometry

def isotropicDispersion (q : ℂ × ℂ) : ℂ := q.1 - Complex.cos q.2

def isotropicInteriorRoot (q : ℂ × ℂ) : ℂ := upperEdgeRoot (isotropicDispersion q)

theorem isotropicInteriorRoot_polynomial (q : ℂ × ℂ) :
    isotropicInteriorRoot q ^ 2 - 2 * isotropicDispersion q * isotropicInteriorRoot q + 1 = 0 :=
  upperEdgeRoot_polynomial _

theorem isotropicInteriorRoot_ne_zero (q : ℂ × ℂ) : isotropicInteriorRoot q ≠ 0 :=
  upperEdgeRoot_ne_zero _

theorem isotropicInteriorRoot_analyticAt (q : ℂ × ℂ)
    (hq : 0 < (isotropicDispersion q).im) : AnalyticAt ℂ isotropicInteriorRoot q :=
  (upperEdgeRoot_analyticAt (edge_discriminant_slit (Or.inl hq))).comp
    (analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd))

theorem isotropicInteriorRoot_unique (q : ℂ × ℂ)
    (hq : 0 < (isotropicDispersion q).im) (r : ℂ)
    (hr : r ^ 2 - 2 * isotropicDispersion q * r + 1 = 0) (hn : ‖r‖ < 1) :
    r = isotropicInteriorRoot q :=
  reciprocal_small_root_unique hr (isotropicInteriorRoot_polynomial q) hn
    (upperEdgeRoot_norm_lt_one hq)

theorem isotropicDispersion_contour_im (S : ℂ) (θ h : ℝ) :
    (isotropicDispersion (S, (θ : ℂ) - Complex.I * (h : ℂ))).im =
      S.im - Real.sinh h * Real.sin θ := by
  have hw : (θ : ℂ) - Complex.I * (h : ℂ) = (θ : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold isotropicDispersion
  rw [hw, Complex.cos_add_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
    sub_zero, mul_one, Real.sinh_neg]
  ring

theorem sinh_mul_nonpos_of_mul_nonpos {h s : ℝ} (hs : h * s ≤ 0) :
    Real.sinh h * s ≤ 0 := by
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have hs0 : 0 ≤ s := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hh.le) hs0
  · simp
  · have hs0 : s ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.sinh_nonneg_iff.mpr hh.le) hs0

variable {ι : Type*} [Fintype ι]

/-- The bump sign conditions are exactly those of an upper bump and its
reflected lower bump. They imply the actual balanced shift has the
opposite sign to sin(theta), with all populations still differentiated. -/
theorem balancedShift_sine_nonpos (scale : ℝ) (θ p m : ι → ℝ)
    (hs : 0 ≤ scale) (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    (hpSin : ∀ i, 0 ≤ p i * Real.sin (θ i))
    (hmSin : ∀ i, m i * Real.sin (θ i) ≤ 0) (i : ι) :
    balancedShift scale p m i * Real.sin (θ i) ≤ 0 := by
  have hP : 0 ≤ ∑ j, p j := Finset.sum_nonneg fun j _ => hp j
  have hQ : 0 ≤ ∑ j, m j := Finset.sum_nonneg fun j _ => hm j
  have h₁ := mul_nonpos_of_nonneg_of_nonpos hP (hmSin i)
  have h₂ := mul_nonneg hQ (hpSin i)
  have h₃ : (∑ j, p j) * (m i * Real.sin (θ i)) -
      (∑ j, m j) * (p i * Real.sin (θ i)) ≤ 0 := by linarith
  have h₄ := mul_nonpos_of_nonneg_of_nonpos hs h₃
  simpa only [balancedShift] using (show
    scale * ((∑ j, p j) * m i - (∑ j, m j) * p i) * Real.sin (θ i) ≤ 0 by
      nlinarith [h₄])

def balancedHomotopyCoordinate (τ : ℝ) (θ p m : ι → ℝ) (ξ : ℝ) (i : ι) : ℂ :=
  contourCoordinate θ (balancedShift (ξ * (τ / Fintype.card ι)) p m) i

theorem balancedHomotopyCoordinate_sum (τ ξ : ℝ) (θ p m : ι → ℝ) :
    ∑ i, balancedHomotopyCoordinate τ θ p m ξ i = ((∑ i, θ i : ℝ) : ℂ) :=
  sum_contourCoordinate θ (ξ * (τ / Fintype.card ι)) p m

theorem balancedHomotopyCoordinate_product (τ ξ : ℝ) (θ p m : ι → ℝ) :
    (∏ i, Complex.exp (balancedHomotopyCoordinate τ θ p m ξ i * Complex.I)) =
      Complex.exp (((∑ i, θ i : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum, ← Finset.sum_mul, balancedHomotopyCoordinate_sum]

/-- The entire actual constrained homotopy stays in Im(W)>0. No lower
bound on an individual bump population, and no restriction on N, is used. -/
theorem balancedHomotopy_dispersion_im_pos (S : ℂ) (hS : 0 < S.im)
    (τ ξ : ℝ) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (θ p m : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    (hpSin : ∀ i, 0 ≤ p i * Real.sin (θ i))
    (hmSin : ∀ i, m i * Real.sin (θ i) ≤ 0) (i : ι) :
    0 < (isotropicDispersion (S, balancedHomotopyCoordinate τ θ p m ξ i)).im := by
  have hs : 0 ≤ ξ * (τ / (Fintype.card ι : ℝ)) := by positivity
  have hsign := balancedShift_sine_nonpos (ξ * (τ / Fintype.card ι)) θ p m
    hs hp hm hpSin hmSin i
  have hsin := sinh_mul_nonpos_of_mul_nonpos hsign
  rw [balancedHomotopyCoordinate, contourCoordinate, isotropicDispersion_contour_im]
  linarith

theorem balancedHomotopy_root_data (S : ℂ) (hS : 0 < S.im)
    (τ ξ : ℝ) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (θ p m : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    (hpSin : ∀ i, 0 ≤ p i * Real.sin (θ i))
    (hmSin : ∀ i, m i * Real.sin (θ i) ≤ 0) :
    (∀ i, AnalyticAt ℂ isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i) ∧
      ‖isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i)‖ < 1 ∧
      isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i) ≠ 0 ∧
      1 - isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i) ^ 2 ≠ 0) ∧
    ∀ i j, 1 - isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i) *
      isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ j) ≠ 0 := by
  have him := balancedHomotopy_dispersion_im_pos S hS τ ξ hτ hξ θ p m hp hm hpSin hmSin
  constructor
  · intro i
    refine ⟨isotropicInteriorRoot_analyticAt _ (him i), upperEdgeRoot_norm_lt_one (him i),
      isotropicInteriorRoot_ne_zero _, ?_⟩
    simpa only [isotropicInteriorRoot, pow_two] using
      upperEdgeRoot_pair_denominator (Or.inl (him i)) (Or.inl (him i))
  · intro i j
    exact upperEdgeRoot_pair_denominator (Or.inl (him i)) (Or.inl (him j))

/-- The signed product kernel is regular for both physical signs along
the whole actual homotopy. N=1 is included. -/
theorem balancedHomotopy_product_denominator [Nonempty ι]
    (S : ℂ) (hS : 0 < S.im) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (τ ξ : ℝ) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (θ p m : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    (hpSin : ∀ i, 0 ≤ p i * Real.sin (θ i))
    (hmSin : ∀ i, m i * Real.sin (θ i) ≤ 0) :
    1 - σ * ∏ i, isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i) ≠ 0 := by
  have hd := (balancedHomotopy_root_data S hS τ ξ hτ hξ θ p m hp hm hpSin hmSin).1
  have hprod : ‖∏ i, isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i)‖ < 1 := by
    rw [norm_prod]
    have h := Finset.prod_lt_prod₀
      (s := (Finset.univ : Finset ι))
      (f := fun i => ‖isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i)‖)
      (g := fun _ => (1 : ℝ))
      (fun i _ => norm_pos_iff.mpr (hd i).2.2.1)
      (fun i _ => (hd i).2.1.le)
      ⟨Classical.arbitrary ι, Finset.mem_univ _, (hd (Classical.arbitrary ι)).2.1⟩
    simpa using h
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul] at he
  have hmul := mul_le_mul_of_nonneg_right hσ
    (norm_nonneg (∏ i, isotropicInteriorRoot (S, balancedHomotopyCoordinate τ θ p m ξ i)))
  linarith

end IsingBulk.AnisoF002.Isotropic
