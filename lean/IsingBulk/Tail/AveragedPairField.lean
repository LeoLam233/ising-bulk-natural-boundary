import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
variable {ι E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def pairSquareMass (s : Finset ι) (d : ι → ℝ) : ℝ := ∑ p ∈ s, (d p)^2

def cancelledAverageField (s : Finset ι) (d : ι → ℝ) (W : ι → E) : E :=
  ∑ p ∈ s, (d p/pairSquareMass s d) • W p

lemma pairSquareWeights_sum (s : Finset ι) (d : ι → ℝ)
    (hS : pairSquareMass s d ≠ 0) : ∑ p ∈ s, (d p)^2/pairSquareMass s d = 1 := by
  rw [← Finset.sum_div]
  exact div_self hS

/-- The selected pole is canceled before defining the field. At zero selected
separation its summand is zero, and no singular vector value is required. -/
lemma cancelledAverageField_freezes (s : Finset ι) (d : ι → ℝ) (W : ι → E)
    (hS : pairSquareMass s d ≠ 0) (L : E →ₗ[ℝ] F) (target : F)
    (hW : ∀ p ∈ s, d p ≠ 0 → L (W p)=d p • target) :
    L (cancelledAverageField s d W)=target := by
  unfold cancelledAverageField
  rw [map_sum]
  have he : ∑ p ∈ s, L ((d p/pairSquareMass s d) • W p)=
      ∑ p ∈ s, ((d p)^2/pairSquareMass s d) • target := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hd : d p=0
    · simp [hd]
    · rw [map_smul,hW p hp hd,smul_smul]
      congr 1
      ring
  rw [he,← Finset.sum_smul,pairSquareWeights_sum s d hS,one_smul]

lemma cancelledAverageField_freezes_two (s : Finset ι) (d : ι → ℝ) (W : ι → E)
    (hS : pairSquareMass s d ≠ 0) (L1 L2 : E →ₗ[ℝ] F) (target1 target2 : F)
    (hW : ∀ p ∈ s, d p ≠ 0 →
      L1 (W p)=d p • target1 ∧ L2 (W p)=d p • target2) :
    L1 (cancelledAverageField s d W)=target1 ∧ L2 (cancelledAverageField s d W)=target2 :=
  ⟨cancelledAverageField_freezes s d W hS L1 target1 (fun p hp hd => (hW p hp hd).1),
    cancelledAverageField_freezes s d W hS L2 target2 (fun p hp hd => (hW p hp hd).2)⟩

lemma cancelledAverageField_eq_weighted (s : Finset ι) (d : ι → ℝ) (W V : ι → E)
    (hW : ∀ p ∈ s, d p ≠ 0 → W p=d p • V p) :
    cancelledAverageField s d W = ∑ p ∈ s, ((d p)^2/pairSquareMass s d) • V p := by
  unfold cancelledAverageField
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hd : d p=0
  · simp [hd]
  · rw [hW p hp hd,smul_smul]
    congr 1
    ring

section Norm
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma pair_weight_inv_sqrt_bound (s : Finset ι) (d : ι → ℝ)
    (hS : 0 < pairSquareMass s d) (p : ι) (hp : p ∈ s) :
    |d p/pairSquareMass s d| ≤ (Real.sqrt (pairSquareMass s d))⁻¹ := by
  classical
  have hsq : (d p)^2 ≤ pairSquareMass s d :=
    Finset.single_le_sum (fun q _ => sq_nonneg (d q)) hp
  have hsqrt := Real.sq_sqrt hS.le
  have hpos := Real.sqrt_pos.mpr hS
  have hab : |d p| ≤ Real.sqrt (pairSquareMass s d) := by
    nlinarith [sq_abs (d p),abs_nonneg (d p)]
  rw [abs_div,abs_of_pos hS]
  apply (div_le_iff₀ hS).mpr
  have he : (Real.sqrt (pairSquareMass s d))⁻¹*pairSquareMass s d =
      Real.sqrt (pairSquareMass s d) := by
    calc
      _ = (Real.sqrt (pairSquareMass s d))⁻¹*(Real.sqrt (pairSquareMass s d))^2 := by rw [hsqrt]
      _ = _ := by field_simp
  rw [he]
  exact hab

/-- One inverse full-equality scale, with only the finite pair count lost. -/
lemma cancelledAverageField_norm (s : Finset ι) (d : ι → ℝ) (W : ι → G)
    (hS : 0 < pairSquareMass s d) (C : ℝ) (_hC : 0 ≤ C)
    (hW : ∀ p ∈ s, ‖W p‖ ≤ C) :
    ‖cancelledAverageField s d W‖ ≤ s.card*C/(Real.sqrt (pairSquareMass s d)) := by
  unfold cancelledAverageField
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ s, (Real.sqrt (pairSquareMass s d))⁻¹*C := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (pair_weight_inv_sqrt_bound s d hS p hp) (hW p hp)
        (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

end Norm
end
end IsingBulk.Tail
