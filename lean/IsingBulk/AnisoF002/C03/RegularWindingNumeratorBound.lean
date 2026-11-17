import IsingBulk.AnisoF002.C03.RegularWindingNumeratorLog
import IsingBulk.AnisoF002.C03.NegativeGlobalPhase
import IsingBulk.AnisoF002.C03.NegativeCenterAmplitude

/-!
# Actual all-winding complete numerator bound

The physical b(T)^(N^2), all one-body factors, every complete pair,
N!, and the original independent-angle normalization remain literal.
The bound is simultaneous in every positive particle number and every
real angular tuple; no zero-sum or first-winding restriction occurs.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def realWindingVandermondeSquared (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∏ ij ∈ indexPairs n, (v ij.1 - v ij.2) ^ 2

theorem realWindingVandermondeSquared_nonneg (n : ℕ) (v : Fin n → ℝ) :
    0 ≤ realWindingVandermondeSquared n v := Finset.prod_nonneg (fun _ij _ => sq_nonneg _)

theorem norm_complexVandermondeSquared_real (n : ℕ) (v : Fin n → ℝ) :
    ‖complexVandermondeSquared n (fun i => (v i : ℂ))‖ = realWindingVandermondeSquared n v := by
  unfold complexVandermondeSquared realWindingVandermondeSquared
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro ij _
  rw [norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def allWindingCenterMagnitude (n : ℕ) (b₀ : ℂ) (φ : ℝ) : ℝ :=
  ‖b₀‖ ^ (n ^ 2) /
    ((n.factorial : ℝ) * (2 * Real.pi) ^ (n - 1) * (2 : ℝ) ^ (n * (n - 1)) *
      (Real.sin φ) ^ (n ^ 2))

theorem norm_windingNormalization (n : ℕ) :
    ‖windingNormalization n‖ = (n.factorial : ℝ) * (2 * Real.pi) ^ (n - 1) := by
  simp only [windingNormalization, norm_mul, norm_natCast, norm_pow, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

theorem real_center_hyperbolic_norm_factors (n : ℕ) (s : ℝ) :
    (1 / s) ^ n * (1 / (2 * s)) ^ (2 * n.choose 2) =
      1 / ((2 : ℝ) ^ (n * (n - 1)) * s ^ (n ^ 2)) := by
  calc
    _ = 1 / (s ^ n * (2 * s) ^ (2 * n.choose 2)) := by
      simp only [one_div_pow]
      ring
    _ = 1 / ((2 : ℝ) ^ (2 * n.choose 2) * s ^ (n + 2 * n.choose 2)) := by
      rw [pow_add, mul_pow]
      ring
    _ = _ := by rw [one_body_pair_degree, twice_choose_two]

theorem filledNegativeNumerator_origin_norm (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ)
    {φ : ℝ} (hφ : 0 < φ) (hπ : φ < Real.pi) (hcenter : g (0, 0) = (φ : ℂ) * Complex.I) :
    ‖filledNegativeNumerator n b g 0 0 0‖ = allWindingCenterMagnitude n (b 0) φ := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hγ : ‖Complex.sinh ((φ : ℂ) * Complex.I)‖ = Real.sin φ := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hsin.le]
  rw [filledNegativeNumerator_center n b g 0 0 ((φ : ℂ) * Complex.I) hcenter]
  simp only [norm_mul, norm_div, norm_pow, norm_one, hγ, Complex.norm_ofNat,
    norm_windingNormalization]
  rw [mul_assoc, real_center_hyperbolic_norm_factors]
  unfold allWindingCenterMagnitude
  ring

theorem exists_actual_all_winding_numerator_bound {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ v : Fin n → ℝ, ∀ T : ℂ,
      (∑ i, v i ^ 2) ≤ s → ‖T‖ ≤ (∑ i, v i ^ 2) / (n : ℝ) →
      ‖completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))‖ ≤
        ‖filledNegativeNumerator n b (negativeGlobalPhase B φ) 0 0 0‖ *
          realWindingVandermondeSquared n v * Real.exp (C * (n : ℝ) * (∑ i, v i ^ 2)) := by
  let g := negativeGlobalPhase B φ
  have hsin : Real.sin φ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hφ hπ).ne'
  have hB0 : B 0 ≠ 0 := by intro hz; simp [hz] at hBi
  have hb0 : b 0 ≠ 0 := by
    intro hz
    have hh := hbsq 0
    rw [hz, zero_pow (by norm_num)] at hh
    exact hB0 hh.symm
  have hg := negativeGlobalPhase_analyticAt_zero hB hφ hπ
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by
    simpa [g] using negativeGlobalPhase_center B hφ hπ (0 : ℂ)
  have hc := physical_negative_phase_temperature_derivative_ne_zero hsin hB hB0 hg hg0
    (Eventually.of_forall (negativeGlobalPhase_cosh B φ))
  have hγ : Complex.sinh ((φ : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hsin) Complex.I_ne_zero
  obtain ⟨L, σ, C, hσ, hC, hbound⟩ := exists_uniform_even_origin_numerator_bound hb hb0 hg hg0 hc
    (negativeGlobalPhase_even B φ) hγ
  refine ⟨σ ^ 2 / 4, C, by positivity, hC, ?_⟩
  intro n hn v T hS hT
  have hQ : displacementSquare n (fun i => (v i : ℂ)) < σ ^ 2 := by
    rw [real_displacement_square]
    nlinarith
  have hT' : ‖T‖ ≤ displacementSquare n (fun i => (v i : ℂ)) / (n : ℝ) := by
    rwa [real_displacement_square]
  have hh := (hbound n hn (fun i => (v i : ℂ)) hQ T hT').2.2.2
  rw [real_displacement_square] at hh
  rw [completeNegativeNumerator_factorization, norm_mul, norm_complexVandermondeSquared_real]
  calc
    _ ≤ realWindingVandermondeSquared n v *
        (‖filledNegativeNumerator n b g 0 0 0‖ * Real.exp (C * (n : ℝ) * (∑ i, v i ^ 2))) :=
      mul_le_mul_of_nonneg_left hh (realWindingVandermondeSquared_nonneg n v)
    _ = _ := by ring

theorem exists_actual_all_winding_numerator_bound_explicit {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ v : Fin n → ℝ, ∀ T : ℂ,
      (∑ i, v i ^ 2) ≤ s → ‖T‖ ≤ (∑ i, v i ^ 2) / (n : ℝ) →
      ‖completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))‖ ≤
        allWindingCenterMagnitude n (b 0) φ * realWindingVandermondeSquared n v *
          Real.exp (C * (n : ℝ) * (∑ i, v i ^ 2)) := by
  obtain ⟨s, C, hs, hC, h⟩ := exists_actual_all_winding_numerator_bound hb hB hφ hπ hBi hbsq
  refine ⟨s, C, hs, hC, ?_⟩
  intro n hn v T hS hT
  have hg0 : negativeGlobalPhase B φ (0, 0) = (φ : ℂ) * Complex.I := by
    simpa using negativeGlobalPhase_center B hφ hπ (0 : ℂ)
  simpa only [filledNegativeNumerator_origin_norm n b (negativeGlobalPhase B φ) hφ hπ hg0] using
    h n hn v T hS hT

end
end IsingBulk.AnisoF002.NegativeHT
