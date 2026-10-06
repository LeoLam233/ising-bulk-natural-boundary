import IsingBulk.Tail.SelectedFCompactMotion
import IsingBulk.Tail.CompactPairGap

/-! Uniform two-coordinate Schur-kernel motion near compact physical roots.
The perturbed roots may lie outside the unit disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem pairKernel_two_coordinate_motion {z w z' w' : ℂ} {g δ : ℝ}
    (hg : 0 < g) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδg : δ ≤ g/6)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hz' : ‖z'-z‖ ≤ δ) (hw' : ‖w'-w‖ ≤ δ)
    (hgap : g ≤ ‖1-z*w‖) :
    ‖pairKernel z' w'-pairKernel z w‖ ≤ (4/g+12/g^2)*δ := by
  have hwp : ‖w'‖ ≤ 2 := by
    have hh := norm_sub_norm_le w' w
    linarith
  have hdenmove : ‖(1-z*w)-(1-z'*w')‖ ≤ 3*δ := by
    have he : (1-z*w)-(1-z'*w')=(z'-z)*w'+z*(w'-w) := by ring
    rw [he]
    calc
      _ ≤ ‖(z'-z)*w'‖+‖z*(w'-w)‖ := norm_add_le _ _
      _ = ‖z'-z‖*‖w'‖+‖z‖*‖w'-w‖ := by rw [norm_mul,norm_mul]
      _ ≤ δ*2+1*δ := add_le_add
        (mul_le_mul hz' hwp (norm_nonneg _) hδ)
        (mul_le_mul hz hw' (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hgap' : g/2 ≤ ‖1-z'*w'‖ := by
    have hh := norm_sub_norm_le (1-z*w) (1-z'*w')
    linarith
  have hd0 : 1-z*w ≠ 0 := norm_pos_iff.mp (hg.trans_le hgap)
  have hd'0 : 1-z'*w' ≠ 0 := norm_pos_iff.mp ((half_pos hg).trans_le hgap')
  have hnum : ‖(z'-w')-(z-w)‖ ≤ 2*δ := by
    have he : (z'-w')-(z-w)=(z'-z)-(w'-w) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hnbase : ‖z-w‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have he : pairKernel z' w'-pairKernel z w =
      ((z'-w')-(z-w))/(1-z'*w')+
        (z-w)*((1-z*w)-(1-z'*w'))/((1-z'*w')*(1-z*w)) := by
    unfold pairKernel
    field_simp
    ring
  have hfirst : ‖((z'-w')-(z-w))/(1-z'*w')‖ ≤ (2*δ)/(g/2) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (half_pos hg) hgap'
  have hdenprod : (g/2)*g ≤ ‖(1-z'*w')*(1-z*w)‖ := by
    rw [norm_mul]
    exact mul_le_mul hgap' hgap hg.le (norm_nonneg _)
  have hsecond : ‖(z-w)*((1-z*w)-(1-z'*w'))/((1-z'*w')*(1-z*w))‖ ≤
      (6*δ)/((g/2)*g) := by
    rw [norm_div,norm_mul]
    apply div_le_div₀ (by positivity) _ (by positivity) hdenprod
    have hh := mul_le_mul hnbase hdenmove (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    nlinarith only [hh]
  rw [he]
  calc
    _ ≤ ‖((z'-w')-(z-w))/(1-z'*w')‖+
        ‖(z-w)*((1-z*w)-(1-z'*w'))/((1-z'*w')*(1-z*w))‖ := norm_add_le _ _
    _ ≤ (2*δ)/(g/2)+(6*δ)/((g/2)*g) := add_le_add hfirst hsecond
    _ = _ := by field_simp; ring

end
end IsingBulk.Tail
