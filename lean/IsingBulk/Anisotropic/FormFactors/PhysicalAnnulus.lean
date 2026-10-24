import IsingBulk.Anisotropic.FormFactors.PhysicalRoots
import IsingBulk.Tail.RightExteriorRoots

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail

def realContourW (B C : ℝ) (y : ℂ) : ℂ := (C:ℂ)-(B:ℂ)*((y+y⁻¹)/2)
def realContourRoot (B C : ℝ) (y : ℂ) : ℂ := compactLeftRoot (realContourW B C y)
def realContourDispersion (B C : ℝ) (x y : ℂ) : ℂ := realContourW B C y-(x+x⁻¹)/2

theorem physical_margin_radius {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (B+1)*(1+r⁻¹)/2 < C := by
  have hC : 0 < C := by linarith
  let a := (B+1)/C
  have ha : 0 < a := div_pos (by linarith) hC
  have ha1 : a < 1 := (div_lt_one hC).mpr (by linarith)
  obtain ⟨r,har,hr1⟩ := exists_between ha1
  have hr : 0 < r := ha.trans har
  have hbr : B+1 < C*r := by nlinarith [(div_lt_iff₀ hC).mp har]
  refine ⟨r,hr,hr1,?_⟩
  have hi : B+1 < (B+1)*r⁻¹ := by
    have hi := (one_lt_inv₀ hr).mpr hr1
    nlinarith
  have hm : (B+1)*r⁻¹ < C := by
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ hr).mpr (by nlinarith)
  nlinarith

theorem realContourW_re_gt_one {B C r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r < 1)
    (hm : (B+1)*(1+r⁻¹)/2 < C) {y : ℂ} (hy : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 1) :
    1 < (realContourW B C y).re := by
  have ht := (Complex.re_le_norm ((y+y⁻¹)/2)).trans (annular_half_trace_norm hr hy hy1)
  have hi := (one_lt_inv₀ hr).mpr hr1
  have hb := mul_le_mul_of_nonneg_left ht hB
  simp only [realContourW,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith

theorem realContourDispersion_re_pos {B C r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    (hm : (B+1)*(1+r⁻¹)/2 < C) {x y : ℂ}
    (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ 1) (hy : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 1) :
    0 < (realContourDispersion B C x y).re := by
  have hxt := (Complex.re_le_norm ((x+x⁻¹)/2)).trans (annular_half_trace_norm hr hx hx1)
  have hyt := (Complex.re_le_norm ((y+y⁻¹)/2)).trans (annular_half_trace_norm hr hy hy1)
  have hb := mul_le_mul_of_nonneg_left hyt hB
  simp only [realContourDispersion,realContourW,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith

theorem realContourRoot_dispersion (B C : ℝ) (y : ℂ) :
    realContourDispersion B C (realContourRoot B C y) y = 0 := by
  have ht := quadratic_root_trace (compactLeftRoot_quadratic (realContourW B C y))
  change realContourRoot B C y+(realContourRoot B C y)⁻¹=2*realContourW B C y at ht
  unfold realContourDispersion
  linear_combination -ht/2

theorem realContourRoot_inside {B C r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r < 1)
    (hm : (B+1)*(1+r⁻¹)/2 < C) {y : ℂ} (hy : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 1) :
    ‖realContourRoot B C y‖ < r := by
  have hn : ‖realContourRoot B C y‖ < 1 :=
    compactLeftRoot_norm_lt_one (realContourW_re_gt_one hB hr hr1 hm hy hy1)
  by_contra hh
  have hpos := realContourDispersion_re_pos hB hr hm (le_of_not_gt hh) hn.le hy hy1
  rw [realContourRoot_dispersion] at hpos
  exact lt_irrefl (0:ℝ) hpos
end
end IsingBulk.Anisotropic.FormFactors
