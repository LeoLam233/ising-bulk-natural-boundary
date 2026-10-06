import IsingBulk.Tail.AllBranchExteriorWeights
import IsingBulk.Tail.GlobalGeometry

/-! Actual maximal separation and mean/shape radius comparisons. These
retain precisely two shape powers per Lie order, with polynomial N loss. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

theorem allBranchExterior_diameter_nonneg {N : ℕ} (u : Fin N → ℝ) :
    0 ≤ allBranchExteriorDiameter u := (allBranchExteriorDiameterNN u).coe_nonneg

theorem allBranchExterior_deviation_le_diameter {N : ℕ} (hN : 0 < N)
    (u : Fin N → ℝ) (i : Fin N) : |u i-branchMean u| ≤ allBranchExteriorDiameter u := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have he : (u i-branchMean u)*(N:ℝ)=∑ j, (u i-u j) := by
    unfold branchMean
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hh := congrArg abs he
  rw [abs_mul,abs_of_pos hNr] at hh
  have hsum : |∑ j, (u i-u j)| ≤ (N:ℝ)*allBranchExteriorDiameter u := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j : Fin N, allBranchExteriorDiameter u := Finset.sum_le_sum (fun j _ => allBranchExterior_pair_le_diameter u i j)
      _ = _ := by simp
  nlinarith

theorem allBranchExterior_shape_diameter_lower {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ) :
    branchShapeRadius u/Real.sqrt (N:ℝ) ≤ allBranchExteriorDiameter u := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := allBranchExterior_diameter_nonneg u
  have hsum : (∑ i, (u i-branchMean u)^2) ≤ (N:ℝ)*(allBranchExteriorDiameter u)^2 := by
    calc
      _ ≤ ∑ _i : Fin N, (allBranchExteriorDiameter u)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := allBranchExterior_deviation_le_diameter hN u i
        nlinarith [sq_abs (u i-branchMean u),abs_nonneg (u i-branchMean u)]
      _ = _ := by simp
  have hh := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul hNr.le,Real.sqrt_sq hd] at hh
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).mpr (by simpa only [branchShapeRadius,mul_comm] using hh)

theorem allBranchExterior_diameter_shape_upper {N : ℕ} (u : Fin N → ℝ) :
    allBranchExteriorDiameter u ≤ 2*branchShapeRadius u := by
  by_cases hd : 0 < allBranchExteriorDiameter u
  · obtain ⟨p,q,_,he⟩ := allBranchExterior_diameter_attained u hd
    rw [← he]
    have hh := abs_sub_le (u p) (branchMean u) (u q)
    rw [abs_sub_comm (branchMean u) (u q)] at hh
    linarith [deviation_le_branchShapeRadius u p,deviation_le_branchShapeRadius u q]
  · have hρ : 0 ≤ branchShapeRadius u := Real.sqrt_nonneg _
    linarith

theorem allBranchExterior_far_diameter_pos {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hu : ρ ≤ branchShapeRadius u) :
    ρ/Real.sqrt (N:ℝ) ≤ allBranchExteriorDiameter u ∧ 0 < allBranchExteriorDiameter u := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hh := (div_le_div_of_nonneg_right hu (Real.sqrt_nonneg _)).trans
    (allBranchExterior_shape_diameter_lower hN u)
  exact ⟨hh,(div_pos hρ (Real.sqrt_pos.mpr hNr)).trans_le hh⟩

end
end IsingBulk.Tail
