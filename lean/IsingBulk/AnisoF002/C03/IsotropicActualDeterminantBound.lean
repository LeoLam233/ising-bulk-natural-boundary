import IsingBulk.AnisoF002.C03.IsotropicBalancedOperatorJets
import IsingBulk.Anisotropic.Algebra.DeterminantBound
import Mathlib.Analysis.Matrix.Normed

/-!
# Exponential bound for the full actual balanced Jacobian

The full population-dependent matrix has uniformly bounded row sums
on one small deformation interval. The already inspected generic Gram
and AM-GM determinant estimates then give a pure exponential bound,
without an unwanted particle-number power or omission of population
derivatives. The historical support is exactly the previously admitted
generic determinant algebra catalogue.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators Matrix Matrix.Norms.Operator ComplexConjugate
open Set

/-- The actual l-infinity operator norm controls each complete matrix
row, retaining every diagonal and population correction. -/
theorem operator_matrix_row_norm_le {N : ℕ}
    (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) (i : Fin N) :
    (∑ j, ‖LinearMap.toMatrix' f.toLinearMap i j‖) ≤ ‖f‖ := by
  have hh : (∑ j, ‖LinearMap.toMatrix' f.toLinearMap i j‖₊) ≤
      (Finset.univ.sup fun k : Fin N => ∑ j, ‖LinearMap.toMatrix' f.toLinearMap k j‖₊) :=
    Finset.le_sup (f := fun k : Fin N => ∑ j, ‖LinearMap.toMatrix' f.toLinearMap k j‖₊)
      (Finset.mem_univ i)
  rw [← Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_toMatrix] at hh
  have hr := NNReal.coe_le_coe.mpr hh
  simpa only [NNReal.coe_sum, coe_nnnorm] using hr

/-- A generic determinant bound from row norms; the finite-dimensional
estimate is applied to the actual l-infinity operator. -/
theorem operator_det_norm_le_pow {N : ℕ} (hN : 0 < N)
    (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) {C : ℝ} (hC : 0 ≤ C) (hf : ‖f‖ ≤ C) :
    ‖f.toLinearMap.det‖ ≤ C ^ N := by
  let A := LinearMap.toMatrix' f.toLinearMap
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrow (i : Fin N) : (∑ j, ‖A i j‖ ^ 2) ≤ C ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg (A i j))).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => norm_nonneg (A i j))
        ((operator_matrix_row_norm_le f i).trans hf) 2)
  have htrace : (Aᴴ * A).trace.re ≤ (N : ℝ) * C ^ 2 := by
    rw [IsingBulk.Anisotropic.Algebra.gram_trace_re, Finset.sum_comm]
    calc
      (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ ∑ _i : Fin N, C ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hmean : (Aᴴ * A).trace.re / Fintype.card (Fin N) ≤ C ^ 2 := by
    rw [Fintype.card_fin]
    exact (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using htrace)
  have hs := IsingBulk.Anisotropic.Algebra.norm_det_sq_le_trace_mean_pow A
    (by simpa only [Fintype.card_fin] using hN)
  have hnonneg : 0 ≤ (Aᴴ * A).trace.re / Fintype.card (Fin N) := by
    rw [IsingBulk.Anisotropic.Algebra.gram_trace_re]
    positivity
  have hh := hs.trans (pow_le_pow_left₀ hnonneg hmean (Fintype.card (Fin N)))
  rw [Fintype.card_fin] at hh
  have hp : (C ^ 2) ^ N = (C ^ N) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 N]
  rw [hp] at hh
  have hnorm := (sq_le_sq₀ (norm_nonneg A.det) (pow_nonneg hC N)).mp hh
  simpa only [A, LinearMap.det_toMatrix'] using hnorm

/-- One deformation radius, selected after the bump width but before N,
bounds the complete actual determinant by 2^N on every angular tuple. -/
theorem exists_actual_balanced_determinant_bound (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ θ : Fin N → ℝ,
        ‖(actualBalancedJacobian η τ ξ θ).det‖ ≤ (2 : ℝ) ^ N := by
  obtain ⟨δ, hδ, hδ1, hnear⟩ := exists_actual_balanced_operator_near_one η
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro N hN τ ξ hτ hξ θ
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hnorm : ‖actualBalancedOperator η τ ξ θ‖ ≤ (2 : ℝ) := by
    calc
      ‖actualBalancedOperator η τ ξ θ‖ = ‖(actualBalancedOperator η τ ξ θ - 1) + 1‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖actualBalancedOperator η τ ξ θ - 1‖ + ‖(1 : AngularOperator N)‖ := norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) + 1 := add_le_add (hnear N hN τ ξ hτ hξ θ) (le_of_eq norm_one)
      _ ≤ 2 := by norm_num
  exact operator_det_norm_le_pow hN (actualBalancedOperator η τ ξ θ) (by norm_num) hnorm

end IsingBulk.AnisoF002.Isotropic
