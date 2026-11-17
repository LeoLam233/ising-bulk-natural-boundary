import IsingBulk.AnisoF002.C03.IsotropicFullDensityFiber
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual fiber set integrals and independent remaining-coordinate measure

The compact fiber estimate is converted to its literal Lebesgue set
integral. The remaining finite box has the exact product measure, whose
independent branch-weight integral gives the required power of Delta.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem exists_actual_full_density_fiber_setIntegral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < W ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N), i ≠ j → ∀ r γ : ℝ, 0 < r →
        (∫ t in fullExtremeFiber θ i j b δ r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ (constrainedAngleLine θ i j t)) ≤
        (C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r * (1 + |Real.log ε|)) *
          independentRemainingWeight W ε b θ i j := by
  obtain ⟨δ, C, W, hδ, hδ1, hC, hW, hbound⟩ :=
    exists_actual_full_density_fiber_integral α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, W, hδ, hδ1, hC, hW, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ hr
  by_cases hne : (fullExtremeFiber θ i j b δ r).Nonempty
  · obtain ⟨A, B, hAB, he⟩ := fullExtremeFiber_eq_interval θ i j hij b δ r hne
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
    exact hbound N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ A B hr hAB
      (by rw [he])
  · have he : fullExtremeFiber θ i j b δ r = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he, Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (by positivity)
      (independentRemainingWeight_nonneg W ε b hW.le θ i j)

def extremeFiberBase {n : ℕ} (a : ℝ) (y : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.snoc (Fin.cons 0 y) (a - ∑ k, y k)

@[simp] theorem extremeFiberBase_first {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    extremeFiberBase a y 0 = 0 := by simp [extremeFiberBase]

@[simp] theorem extremeFiberBase_middle {n : ℕ} (a : ℝ) (y : Fin n → ℝ) (k : Fin n) :
    extremeFiberBase a y k.succ.castSucc = y k := by
  simp only [extremeFiberBase, Fin.snoc_castSucc, Fin.cons_succ]

@[simp] theorem extremeFiberBase_last {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    extremeFiberBase a y (Fin.last (n + 1)) = a - ∑ k, y k := by simp [extremeFiberBase]

theorem extremeFiberBase_sum {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    ∑ k, extremeFiberBase a y k = a := by
  unfold extremeFiberBase
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_add]
  ring

theorem extremeFiberBase_shifted_mean {n : ℕ} (μ b : ℝ) (y : Fin n → ℝ) :
    angularMean (fun k => extremeFiberBase ((n + 2 : ℝ) * (μ - b)) y k + b) = μ := by
  rw [angularMean, Finset.sum_add_distrib, extremeFiberBase_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

theorem extremeFiberBase_remaining_weight {n : ℕ} (a W ε b : ℝ)
    (hW : 0 < W) (hε : 0 < ε) (y : Fin n → ℝ) :
    independentRemainingWeight W ε b (extremeFiberBase a y) 0 (Fin.last (n + 1)) =
      ∏ k, W * branchWeight ε (y k + b) := by
  let f : Fin (n + 2) → ℝ := fun k => W * branchWeight ε (extremeFiberBase a y k + b)
  have hij : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by exact Fin.ne_of_val_ne (by simp)
  have hfirst : f 0 ≠ 0 := by dsimp [f, branchWeight]; positivity
  have hlast : f (Fin.last (n + 1)) ≠ 0 := by dsimp [f, branchWeight]; positivity
  have he := prod_split_extreme_indices 0 (Fin.last (n + 1)) hij f
  have hexpand : (∏ k, f k) = f 0 * f (Fin.last (n + 1)) * ∏ k : Fin n, W * branchWeight ε (y k + b) := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
    simp only [f, Fin.castSucc_zero, extremeFiberBase_middle]
    ring
  rw [hexpand] at he
  exact (mul_left_cancel₀ (mul_ne_zero hfirst hlast) he).symm

def remainingAngularBox (n : ℕ) (μ b r : ℝ) : Set (Fin n → ℝ) :=
  Icc (fun _ => μ - b - 2 * r) (fun _ => μ - b + 2 * r)

theorem remainingAngularBox_eq_pi (n : ℕ) (μ b r : ℝ) :
    remainingAngularBox n μ b r = Set.univ.pi (fun _ => Icc (μ - b - 2 * r) (μ - b + 2 * r)) := by
  ext y
  simp only [remainingAngularBox, mem_Icc, Pi.le_def, mem_univ_pi, forall_and]

theorem remaining_branch_weight_product_integral (n : ℕ) (W ε μ b r : ℝ) (hr : 0 < r) :
    (∫ y in remainingAngularBox n μ b r, ∏ k, W * branchWeight ε (y k + b)) =
      (W * ∫ u in μ - 2 * r..μ + 2 * r, branchWeight ε u) ^ n := by
  rw [remainingAngularBox_eq_pi]
  change (∫ y : Fin n → ℝ, ∏ k, W * branchWeight ε (y k + b)
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ => Icc (μ - b - 2 * r) (μ - b + 2 * r)))) = _
  rw [Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow (ι := Fin n) (fun u : ℝ => W * branchWeight ε (u + b))]
  simp only [Fintype.card_fin]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hr] : μ - b - 2 * r ≤ μ - b + 2 * r),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  congr 2 <;> ring

/-- Exactly N-2 remaining independent angular integrations cost
(C Delta)^(N-2), with no additional parameter or population premise. -/
theorem remaining_branch_weight_product_integral_bound (n : ℕ) (W ε μ b r : ℝ)
    (hW : 0 ≤ W) (hε : 0 < ε) (hr : 0 < r) :
    (∫ y in remainingAngularBox n μ b r, ∏ k, W * branchWeight ε (y k + b)) ≤
      (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  rw [remaining_branch_weight_product_integral n W ε μ b r hr]
  apply pow_le_pow_left₀
  · exact mul_nonneg hW (intervalIntegral.integral_nonneg_of_forall (by linarith only [hr])
      (branchWeight_nonneg ε))
  · have hh := mul_le_mul_of_nonneg_left (branchWeight_shell_integral_bound μ r ε hr hε) hW
    exact hh.trans_eq (by ring)

end IsingBulk.AnisoF002.Isotropic
