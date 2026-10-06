import IsingBulk.Tail.GlobalGeometry

/-! Exponential support inclusions valid at every finite tail order, not
merely eventually in N. The scale B may subsequently be increased to absorb
fixed-jet constants without invalidating these inclusions. -/
namespace IsingBulk.Tail
noncomputable section

def allBranchMicroRadius (A c : ℝ) (N : ℕ) : ℝ :=
  c*Real.exp (-(A+4)*(N:ℝ))/(N:ℝ)
def allBranchEqualityRadius (B : ℝ) (N : ℕ) : ℝ := Real.exp (-B*(N:ℝ))
def allBranchScaleThreshold (A c : ℝ) : ℝ := A+6+|Real.log (16/c)|

theorem allBranchScaleThreshold_gt (A c : ℝ) :
    A+5 < allBranchScaleThreshold A c := by
  unfold allBranchScaleThreshold
  linarith [abs_nonneg (Real.log (16/c))]

theorem all_branch_scale_inclusion {A c B : ℝ} (hc : 0 < c)
    (hB : allBranchScaleThreshold A c ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    2*allBranchEqualityRadius B N ≤ allBranchMicroRadius A c N/8 := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let K := |Real.log (16/c)|
  have hK : 0 ≤ K := abs_nonneg _
  have hlog : Real.log (16/c) ≤ K*(N:ℝ) := by
    have h₁ := le_abs_self (Real.log (16/c))
    have h₂ := mul_le_mul_of_nonneg_left hn hK
    dsimp [K] at *
    nlinarith
  have hfactor : 16/c ≤ Real.exp (K*(N:ℝ)) := by
    rw [← Real.exp_log (by positivity : (0:ℝ)<16/c)]
    exact Real.exp_le_exp.mpr hlog
  have hNexp : (N:ℝ) ≤ Real.exp (2*(N:ℝ)) := by
    have := Real.add_one_le_exp (2*(N:ℝ))
    linarith
  have hprod := mul_le_mul hfactor hNexp (show (0:ℝ) ≤ N by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hf : 16*(N:ℝ) ≤ c*Real.exp ((2+K)*(N:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hprod hc.le
    field_simp at hh
    convert hh using 1; ring
  have hB0 : -(B)*(N:ℝ) ≤ -(allBranchScaleThreshold A c)*(N:ℝ) := by nlinarith
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB0) (by norm_num : (0:ℝ)≤2)).trans
  unfold allBranchMicroRadius
  rw [show -(allBranchScaleThreshold A c)*(N:ℝ) =
    -(A+4)*(N:ℝ)-(2+K)*(N:ℝ) by dsimp [allBranchScaleThreshold,K]; ring,
    Real.exp_sub]
  rw [← mul_div_assoc,div_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity : (0:ℝ)<(N:ℝ)*8)).mpr
  have hh := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(A+4)*(N:ℝ))).le
  nlinarith

theorem all_branch_negative_scale_inclusion {A c B : ℝ} (hc : 0 < c)
    (hB : allBranchScaleThreshold A c ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    allBranchEqualityRadius B N ≤ allBranchMicroRadius A c N/16 := by
  have h := all_branch_scale_inclusion hc hB hN
  linarith

/-- The exact mean/shape support geometry consumes the constructed scales. -/
theorem all_branch_near_scale_common_sign {A c B : ℝ} (hc : 0 < c)
    (hB : allBranchScaleThreshold A c ≤ B) {N : ℕ} (hN : 1 ≤ N)
    (u : Fin N → ℝ) (a : Fin N)
    (ha : allBranchMicroRadius A c N/2 ≤ |u a|)
    (hr : branchShapeRadius u ≤ 2*allBranchEqualityRadius B N) :
    (3*allBranchMicroRadius A c N/8 ≤ branchMean u ∧
        ∀ i, allBranchMicroRadius A c N/4 ≤ u i) ∨
      (branchMean u ≤ -(3*allBranchMicroRadius A c N/8) ∧
        ∀ i, u i ≤ -(allBranchMicroRadius A c N/4)) := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : 0 < allBranchMicroRadius A c N := by unfold allBranchMicroRadius; positivity
  exact near_equality_anchor_common_sign u a hb ha
    (hr.trans (all_branch_scale_inclusion hc hB hN))

end
end IsingBulk.Tail
