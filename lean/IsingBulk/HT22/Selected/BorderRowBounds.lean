import IsingBulk.HT22.Algebra.OddBordered
import IsingBulk.Preferred22.SelectedGaugeBounds
import IsingBulk.Preferred22.SelectedKernelPerturbation

/-! F001 selected-sector row bounds. The ordinary L entries are related to
but not confused with the LT gauge matrix; the two constant borders are
included in Hadamard at dimension N+1, without an even-N hypothesis. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.HT22.Algebra IsingBulk.Preferred22
open scoped BigOperators

theorem ordinaryEntry_norm_sq (yi yj zi zj : ℂ) (hyi : yi≠0) (hyj : yj≠0)
    (hzi : zi≠0) (hzj : zj≠0) :
    ‖ordinaryEntry yi yj zi zj‖^2 =
      (‖yi‖/‖zi‖)*(‖yj‖/‖zj‖)*
        ‖(-Complex.I*Complex.sqrt (zi/yi)*Complex.sqrt (zj/yj)*
          (yi-yj)/(1-zi*zj))‖^2 := by
  have hi : ‖Complex.sqrt (zi/yi)‖^2=‖zi‖/‖yi‖ := by
    rw [←norm_pow,complex_sqrt_sq,norm_div]
  have hj : ‖Complex.sqrt (zj/yj)‖^2=‖zj‖/‖yj‖ := by
    rw [←norm_pow,complex_sqrt_sq,norm_div]
  simp only [ordinaryEntry,dispersionB,norm_mul,norm_neg,Complex.norm_I,one_mul,
    norm_div,mul_pow,div_pow,hi,hj]
  have hyin := norm_ne_zero_iff.mpr hyi
  have hyjn := norm_ne_zero_iff.mpr hyj
  have hzin := norm_ne_zero_iff.mpr hzi
  have hzjn := norm_ne_zero_iff.mpr hzj
  field_simp

 theorem ordinary_rows_of_gauge {N : ℕ} (y z : Fin N → ℂ) {E K C : ℝ}
    (hE : 0≤E) (hK : 0≤K)
    (hy : ∀ i, y i≠0) (hz : ∀ i, z i≠0)
    (hyE : ∀ i, ‖y i‖≤E) (hzK : ∀ i, ‖(z i)⁻¹‖≤K)
    (hrow : ∀ i, (∑ j, ‖gaugeKernel y z i j‖^2)≤C) :
    ∀ i, (∑ j, ‖ordinaryEntry (y i) (y j) (z i) (z j)‖^2)≤(E*K)^2*C := by
  intro i
  have hratio (i : Fin N) : ‖y i‖/‖z i‖≤E*K := by
    rw [div_eq_mul_inv,←norm_inv]
    exact mul_le_mul (hyE i) (hzK i) (norm_nonneg _) hE
  calc
    _ ≤ ∑ j, (E*K)^2*‖gaugeKernel y z i j‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [ordinaryEntry_norm_sq _ _ _ _ (hy i) (hy j) (hz i) (hz j)]
      change (‖y i‖/‖z i‖)*(‖y j‖/‖z j‖)*‖gaugeKernel y z i j‖^2 ≤ _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (mul_le_mul (hratio i) (hratio j) (by positivity) (mul_nonneg hE hK)).trans_eq (by ring)
    _ = (E*K)^2*(∑ j, ‖gaugeKernel y z i j‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)

 theorem ghostBorder_row_squared_bound {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ j, ‖K i j‖^2)≤C^2*N) :
    ∀ i, (∑ j, ‖ghostBorder K (fun _ => 1) i j‖^2)≤(C+1)^2*(N+1) := by
  intro i
  cases i using Fin.cases with
  | zero =>
      simp only [Fin.sum_univ_succ,ghostBorder_zero_zero,norm_zero,zero_pow (by decide : 2≠0),
        ghostBorder_zero_succ,norm_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one,zero_add]
      nlinarith [sq_nonneg C]
  | succ i =>
      simp only [Fin.sum_univ_succ,ghostBorder_succ_zero,norm_neg,norm_one,one_pow,
        ghostBorder_succ_succ]
      nlinarith [hrow i,sq_nonneg C]

 theorem ghostBorder_det_bound {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ j, ‖K i j‖^2)≤C^2*N) :
    ‖(ghostBorder K (fun _ => 1)).det‖≤((C+1)*Real.sqrt (N+1))^(N+1) := by
  have h := preferred_determinant_of_row_squares (Nat.succ_pos N)
    (ghostBorder K (fun _ => 1)) (show 0≤C+1 by linarith)
  have hb : ∀ i, (∑ j, ‖ghostBorder K (fun _ => 1) i j‖^2)≤(C+1)^2*(N.succ:ℝ) := by
    simpa only [Nat.cast_succ] using ghostBorder_row_squared_bound K hC hrow
  simpa only [Nat.cast_succ] using h hb

end
end IsingBulk.HT22.Selected
