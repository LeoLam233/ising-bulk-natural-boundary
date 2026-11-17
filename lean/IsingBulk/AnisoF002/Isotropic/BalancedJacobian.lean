import IsingBulk.AnisoF002.Isotropic.BalancedLipschitz
import IsingBulk.AnisoF002.Isotropic.OccupancyDerivative
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The full balanced angular Jacobian

This is the differential of the actual deformation in frozen F002
§7, immediately after `eq:iso-balanced-deformation`.  Both population
derivatives are retained.  The uniform smallness estimate and inverse
are proved for every finite particle population, without a frozen
occupancy approximation.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Complex-linear extension of the full real displacement differential. -/
def balancedDisplacementDifferential (scale : ℝ) (p m dp dm : ι → ℝ)
    (a : ι → ℂ) (i : ι) : ℂ :=
  (scale : ℂ) *
    (((∑ j, (dp j : ℂ) * a j) * (m i : ℂ) +
      ((∑ j, p j : ℝ) : ℂ) * (dm i : ℂ) * a i) -
     ((∑ j, (dm j : ℂ) * a j) * (p i : ℂ) +
      ((∑ j, m j : ℝ) : ℂ) * (dp i : ℂ) * a i))

/-- The full angular Jacobian, as a complex-linear map. -/
def balancedAngularJacobian (scale : ℝ) (p m dp dm : ι → ℝ) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun a i := a i - Complex.I * balancedDisplacementDifferential scale p m dp dm a i
  map_add' a b := by
    ext i
    simp only [balancedDisplacementDifferential, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    ext i
    simp only [balancedDisplacementDifferential, Pi.smul_apply, smul_eq_mul,
      mul_left_comm _ c, ← Finset.mul_sum, RingHom.id_apply]
    ring

/-- The complete displacement differential preserves the zero-sum plane. -/
theorem sum_balancedDisplacementDifferential (scale : ℝ)
    (p m dp dm : ι → ℝ) (a : ι → ℂ) :
    ∑ i, balancedDisplacementDifferential scale p m dp dm a i = 0 := by
  simp only [balancedDisplacementDifferential, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    Complex.ofReal_sum]
  ring

/-- The actual full Jacobian has the exact left eigenvector `1`. -/
theorem sum_balancedAngularJacobian (scale : ℝ)
    (p m dp dm : ι → ℝ) (a : ι → ℂ) :
    ∑ i, balancedAngularJacobian scale p m dp dm a i = ∑ i, a i := by
  change (∑ i, (a i - Complex.I *
    balancedDisplacementDifferential scale p m dp dm a i)) = _
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_balancedDisplacementDifferential, mul_zero, sub_zero]

/-- Every real differentiable path is differentiated by this same full map. -/
theorem balancedContourPath_derivative_jacobian
    (scale x : ℝ) (θ : ι → ℝ → ℝ) (p m : ℝ → ℝ)
    (a dp dm : ι → ℝ)
    (hθ : ∀ i, HasDerivAt (θ i) (a i) x)
    (hp : ∀ i, HasDerivAt p (dp i) (θ i x))
    (hm : ∀ i, HasDerivAt m (dm i) (θ i x)) (i : ι) :
    HasDerivAt
      (fun t => balancedContourPath scale θ
        (fun j t => p (θ j t)) (fun j t => m (θ j t)) t i)
      (balancedAngularJacobian scale (fun j => p (θ j x))
        (fun j => m (θ j x)) dp dm (fun j => (a j : ℂ)) i) x := by
  have h := balancedContourPath_hasDerivAt scale x θ
    (fun j t => p (θ j t)) (fun j t => m (θ j t)) a
    (fun j => dp j * a j) (fun j => dm j * a j) hθ
    (fun j => (hp j).comp x (hθ j))
    (fun j => (hm j).comp x (hθ j)) i
  convert h using 1
  simp only [balancedAngularJacobian, LinearMap.coe_mk, AddHom.coe_mk,
      balancedDisplacementDifferential, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum]
  ring

/-- A complete weighted population is bounded by `N L R`. -/
theorem norm_weighted_population_le (d : ι → ℝ) (a : ι → ℂ)
    (L R : ℝ) (hL : 0 ≤ L) (_hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ L) (ha : ∀ i, ‖a i‖ ≤ R) :
    ‖∑ i, (d i : ℂ) * a i‖ ≤ (Fintype.card ι : ℝ) * L * R := by
  calc
    ‖∑ i, (d i : ℂ) * a i‖ ≤ ∑ i, ‖(d i : ℂ) * a i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, L * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hd i) (ha i) (norm_nonneg _) hL
    _ = (Fintype.card ι : ℝ) * L * R := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The rank-two correction costs no particle-dependent operator factor:
the exact scale `τ/N` cancels all population sums. -/
theorem balancedDisplacementDifferential_bound
    (p m dp dm : ι → ℝ) (a : ι → ℂ) (τ L R : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (ha : ∀ i, ‖a i‖ ≤ R) (i : ι) :
    ‖balancedDisplacementDifferential (τ / Fintype.card ι) p m dp dm a i‖ ≤
      4 * τ * L * R := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hP := bump_population_bounds p hp
  have hQ := bump_population_bounds m hm
  have hdpS := norm_weighted_population_le dp a L R hL hR hdp ha
  have hdmS := norm_weighted_population_le dm a L R hL hR hdm ha
  have hpm : ‖(m i : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hm i).1] using (hm i).2
  have hpp : ‖(p i : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hp i).1] using (hp i).2
  have hPn : ‖((∑ j, p j : ℝ) : ℂ)‖ ≤ (Fintype.card ι : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP.1]
    exact hP.2
  have hQn : ‖((∑ j, m j : ℝ) : ℂ)‖ ≤ (Fintype.card ι : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ.1]
    exact hQ.2
  have hdpm : ‖(dp i : ℂ)‖ ≤ L := by simpa using hdp i
  have hdmm : ‖(dm i : ℂ)‖ ≤ L := by simpa using hdm i
  have ht1 : ‖(∑ j, (dp j : ℂ) * a j) * (m i : ℂ)‖ ≤
      (Fintype.card ι : ℝ) * L * R := by
    rw [norm_mul]
    exact (mul_le_mul hdpS hpm (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have ht2 : ‖((∑ j, p j : ℝ) : ℂ) * (dm i : ℂ) * a i‖ ≤
      (Fintype.card ι : ℝ) * L * R := by
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul hPn hdmm (norm_nonneg _) hnR.le)
      (ha i) (norm_nonneg _) (by positivity)
  have ht3 : ‖(∑ j, (dm j : ℂ) * a j) * (p i : ℂ)‖ ≤
      (Fintype.card ι : ℝ) * L * R := by
    rw [norm_mul]
    exact (mul_le_mul hdmS hpp (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have ht4 : ‖((∑ j, m j : ℝ) : ℂ) * (dp i : ℂ) * a i‖ ≤
      (Fintype.card ι : ℝ) * L * R := by
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul hQn hdpm (norm_nonneg _) hnR.le)
      (ha i) (norm_nonneg _) (by positivity)
  unfold balancedDisplacementDifferential
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hτ hnR.le)]
  have hs : ‖((∑ j, (dp j : ℂ) * a j) * (m i : ℂ) +
      ((∑ j, p j : ℝ) : ℂ) * (dm i : ℂ) * a i) -
      ((∑ j, (dm j : ℂ) * a j) * (p i : ℂ) +
      ((∑ j, m j : ℝ) : ℂ) * (dp i : ℂ) * a i)‖ ≤
      4 * (Fintype.card ι : ℝ) * L * R := by
    apply (norm_sub_le _ _).trans
    exact (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans (by linarith)
  calc
    _ ≤ (τ / (Fintype.card ι : ℝ)) * (4 * (Fintype.card ι : ℝ) * L * R) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hτ hnR.le)
    _ = 4 * τ * L * R := by field_simp

/-- Uniform operator bound for the full difference from the identity. -/
theorem balancedAngularJacobian_sub_id_bound
    (p m dp dm : ι → ℝ) (a : ι → ℂ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L) :
    ‖balancedAngularJacobian (τ / Fintype.card ι) p m dp dm a - a‖ ≤
      (4 * τ * L) * ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have h := balancedDisplacementDifferential_bound p m dp dm a τ L ‖a‖
    hn hτ hL (norm_nonneg _) hp hm hdp hdm (fun j => norm_le_pi_norm a j) i
  change ‖(a i - Complex.I *
    balancedDisplacementDifferential (τ / Fintype.card ι) p m dp dm a i) - a i‖ ≤ _
  rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul]
  exact h

/-- Every particle-number Jacobian is injective under one fixed smallness choice. -/
theorem balancedAngularJacobian_injective
    (p m dp dm : ι → ℝ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (hsmall : 4 * τ * L < 1) :
    Function.Injective (balancedAngularJacobian (τ / Fintype.card ι) p m dp dm) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have h := balancedAngularJacobian_sub_id_bound p m dp dm a τ L hn hτ hL hp hm hdp hdm
  rw [ha, zero_sub, norm_neg] at h
  have hz : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
  exact norm_eq_zero.mp hz

/-- The full Jacobian is an automorphism of the complex angle space. -/
theorem balancedAngularJacobian_bijective
    (p m dp dm : ι → ℝ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (hsmall : 4 * τ * L < 1) :
    Function.Bijective (balancedAngularJacobian (τ / Fintype.card ι) p m dp dm) := by
  have hi := balancedAngularJacobian_injective p m dp dm τ L hn hτ hL hp hm hdp hdm hsmall
  exact ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

/-- The inverse preserves the exact angular sum.  The comparison of physical
angular measures is a separate determinant and integration obligation. -/
theorem balancedAngularJacobian_inverse_preserves_sum
    (scale : ℝ) (p m dp dm : ι → ℝ) (a b : ι → ℂ)
    (h : balancedAngularJacobian scale p m dp dm a = b) :
    ∑ i, a i = ∑ i, b i := by
  rw [← h, sum_balancedAngularJacobian]

/-- A uniform inverse bound follows from the full, population-dependent
Jacobian estimate. -/
theorem balancedAngularJacobian_inverse_bound
    (p m dp dm : ι → ℝ) (a b : ι → ℂ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (hsmall : 4 * τ * L < 1)
    (h : balancedAngularJacobian (τ / Fintype.card ι) p m dp dm a = b) :
    ‖a‖ ≤ ‖b‖ / (1 - 4 * τ * L) := by
  have hb := balancedAngularJacobian_sub_id_bound p m dp dm a τ L hn hτ hL hp hm hdp hdm
  rw [h] at hb
  have ht : ‖a‖ ≤ ‖b‖ + ‖b - a‖ := by
    simpa only [sub_sub_cancel] using (norm_sub_le b (b - a))
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith

end IsingBulk.AnisoF002.Isotropic
