import IsingBulk.First.GlobalResidueRoot
import IsingBulk.First.RadialDiskAdmissibility
import IsingBulk.Algebra.SchurContinuation
import Mathlib.Tactic

/-! The unrestricted original-torus Schur estimate. The lower half-disk
condition is proved from the actual dispersion, not imposed on y angles. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem schur_normSq_identity (z w : ℂ) :
    Complex.normSq (1-z*w)-Complex.normSq (z-w) =
      (1-Complex.normSq z)*(1-Complex.normSq w)+4*z.im*w.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im]
  ring

theorem lower_half_disk_pair_norm {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (hzi : z.im ≤ 0) (hwi : w.im ≤ 0) : ‖pairKernel z w‖ ≤ 1 := by
  have hzsq : Complex.normSq z ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hwsq : Complex.normSq w ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have hdiff : 0 ≤ Complex.normSq (1-z*w)-Complex.normSq (z-w) := by
    rw [schur_normSq_identity]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hzsq) (sub_nonneg.mpr hwsq))
      (by nlinarith [mul_nonneg_of_nonpos_of_nonpos hzi hwi])
  have hnorm : ‖z-w‖ ≤ ‖1-z*w‖ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm] at hdiff
    nlinarith [norm_nonneg (z-w), norm_nonneg (1-z*w)]
  rw [pairKernel, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (one_sub_mul_ne_zero_of_norm_lt_one hz hw))).mpr hnorm

theorem original_root_lower_half_disk {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s y : ℂ} (hm : r⁻¹-r < (sourceS s).im) (hy : ‖y‖ = r) :
    ‖globalRoot s y‖ < 1 ∧ (globalRoot s y).im < 0 := by
  have hW := sourceW_upper_of_margin hr hr1 hm hy
  exact ⟨interiorRoot_norm_lt_one hW, interiorRoot_lower_im hW⟩

theorem original_root_pair_norm {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s y v : ℂ} (hm : r⁻¹-r < (sourceS s).im) (hy : ‖y‖ = r) (hv : ‖v‖ = r) :
    ‖pairKernel (globalRoot s y) (globalRoot s v)‖ ≤ 1 := by
  obtain ⟨hz,hzi⟩ := original_root_lower_half_disk hr hr1 hm hy
  obtain ⟨hw,hwi⟩ := original_root_lower_half_disk hr hr1 hm hv
  exact lower_half_disk_pair_norm hz hw hzi.le hwi.le

theorem original_root_pairProduct_norm {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖ = r) :
    ‖pairProduct (fun i => globalRoot s (y i))‖ ≤ 1 := by
  unfold pairProduct
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro j _
  exact original_root_pair_norm hr hr1 hm (hy i) (hy j)

end
end IsingBulk.Tail
