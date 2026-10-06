import IsingBulk.Analysis.BranchData
import IsingBulk.First.MeanSelectedData
import IsingBulk.First.ComplementRadialCompact

/-! Actual branch data from the immutable selected family, with precisely
the FIRST source radial constant sin(theta)/4. No geometric estimate is data. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First IsingBulk.PrimeFamily

def selectedLocalBranchData {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) : LocalBranchData where
  theta := Real.arccos (cosineAverage p a b)
  thetaB := branchAngle p a b
  c₀ := Real.sin (Real.arccos (cosineAverage p a b))/4
  tau := τ
  alpha := α
  theta_pos := Real.arccos_pos.mpr (cosineAverage_bounds ha hb).2
  theta_lt := Real.arccos_lt_pi_div_two.mpr (cosineAverage_bounds ha hb).1
  thetaB_pos := Real.arccos_pos.mpr (by have hc := cosineAverage_bounds ha hb; linarith)
  thetaB_lt := Real.arccos_lt_pi.mpr (by have hc := cosineAverage_bounds ha hb; linarith)
  angle_relation := by
    have hc := cosineAverage_bounds ha hb
    rw [branchAngle,Real.cos_arccos (by linarith) (by linarith),
      Real.cos_arccos (by linarith) hc.2.le]
  c₀_pos := by
    have hc := cosineAverage_bounds ha hb
    have ht : 0 < Real.arccos (cosineAverage p a b) := Real.arccos_pos.mpr hc.2
    have htπ : Real.arccos (cosineAverage p a b) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi ht htπ) (by norm_num)
  margin := by
    have hc := cosineAverage_bounds ha hb
    have ht : 0 < Real.arccos (cosineAverage p a b) := Real.arccos_pos.mpr hc.2
    have htπ : Real.arccos (cosineAverage p a b) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    have hs := Real.sin_pos_of_pos_of_lt_pi ht htπ
    have hm := mul_le_mul_of_nonneg_left (Real.sin_le_one (branchAngle p a b)) hs.le
    nlinarith
  tau_pos := hτ
  alpha_pos := hα

theorem selectedLocalBranchData_theta {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (selectedLocalBranchData ha hb τ α hτ hα).theta=(selectedOrderedChart ha hb).theta := rfl

theorem selectedLocalBranchData_c0_small {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (selectedLocalBranchData ha hb τ α hτ hα).c₀ <
      Real.sin (selectedLocalBranchData ha hb τ α hτ hα).theta/2 := by
  have hd := (selectedLocalBranchData ha hb τ α hτ hα).c₀_pos
  change Real.sin (Real.arccos (cosineAverage p a b))/4 <
    Real.sin (Real.arccos (cosineAverage p a b))/2
  change 0 < Real.sin (Real.arccos (cosineAverage p a b))/4 at hd
  linarith

theorem selectedLocalBranchData_source_radius {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α ε : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (sourceRadialPair (selectedOrderedChart ha hb).theta ε).1 =
      Real.exp (-(selectedLocalBranchData ha hb τ α hτ hα).c₀*ε) := rfl

theorem selectedLocalBranchData_branch {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    Complex.exp (-((selectedLocalBranchData ha hb τ α hτ hα).thetaB:ℂ)*Complex.I)=
      selectedBranch p a b := rfl

end
end IsingBulk.Tail
