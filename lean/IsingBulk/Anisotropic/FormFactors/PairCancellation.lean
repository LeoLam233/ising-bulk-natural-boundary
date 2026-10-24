import IsingBulk.Anisotropic.FormFactors.PhysicalAnnulus

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail

theorem anisotropic_pair_cancellation {B C : ℝ} {y w u v : ℂ}
    (hy : y ≠ 0) (hw : w ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hyw : 1-y*w ≠ 0) (huv : 1-u*v ≠ 0)
    (htu : u+u⁻¹=2*realContourW B C y) (htv : v+v⁻¹=2*realContourW B C w) :
    pairKernel u v * pairKernel y w = (B:ℂ)*canceledPair y w u v := by
  have hrel : (u-v)*(1-u*v)*y*w = -(B:ℂ)*(y-w)*(1-y*w)*u*v := by
    have hh := congrArg₂ (fun a b : ℂ => a-b) htu htv
    unfold realContourW at hh
    field_simp [hu,hv,hy,hw] at hh
    linear_combination -hh
  unfold pairKernel canceledPair
  field_simp [huv,hyw,hy,hw]
  linear_combination (y-w)*hrel

/-- On the inner circle this is the original pair product, while its
right-hand side continues regularly through every reciprocal-angle collision. -/
theorem realContourRoot_pair_cancellation {B C r : ℝ} (hB : 0 ≤ B)
    (hr : 0 < r) (hr1 : r < 1) (hm : (B+1)*(1+r⁻¹)/2 < C)
    {y w : ℂ} (hy : ‖y‖=r) (hw : ‖w‖=r) :
    pairKernel (realContourRoot B C y) (realContourRoot B C w)*pairKernel y w =
      (B:ℂ)*canceledPair y w (realContourRoot B C y) (realContourRoot B C w) := by
  have hru := realContourRoot_inside hB hr hr1 hm hy.ge (hy.le.trans hr1.le)
  have hrv := realContourRoot_inside hB hr hr1 hm hw.ge (hw.le.trans hr1.le)
  exact anisotropic_pair_cancellation
    (norm_ne_zero_iff.mp (hy.trans_ne hr.ne')) (norm_ne_zero_iff.mp (hw.trans_ne hr.ne'))
    (compactLeftRoot_nonzero _) (compactLeftRoot_nonzero _)
    (one_sub_mul_ne_zero_of_norm_lt_one (hy.trans_lt hr1) (hw.trans_lt hr1))
    (one_sub_mul_ne_zero_of_norm_lt_one (hru.trans hr1) (hrv.trans hr1))
    (quadratic_root_trace (compactLeftRoot_quadratic _))
    (quadratic_root_trace (compactLeftRoot_quadratic _))
end
end IsingBulk.Anisotropic.FormFactors
