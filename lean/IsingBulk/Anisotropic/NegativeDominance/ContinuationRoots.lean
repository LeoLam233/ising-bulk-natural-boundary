import IsingBulk.Anisotropic.NegativeDominance.OddMomentum
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularHolomorphy

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators Topology

def continuedTransferRoot (lam : ℝ) (z q : ℂ) : ℂ := continuedRoot (transferW lam z q)

theorem negative_transferW_eq_edgeW {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z) (q : ℝ) :
    transferW lam z (q : ℂ)=edgeW b (-spectralT lam z/spectralS z) (q-Real.pi) := by
  unfold transferW edgeW
  rw [← Complex.ofReal_cos, Real.cos_sub_pi]
  push_cast
  field_simp [hS]
  linear_combination hedge

theorem continuedTransferRoot_eq_edgeRoot {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z) (q : ℝ) :
    continuedTransferRoot lam z (q : ℂ)=edgeRoot b (-spectralT lam z/spectralS z) (q-Real.pi) := by
  unfold continuedTransferRoot edgeRoot
  rw [negative_transferW_eq_edgeW hS hedge]

theorem transferW_joint_analyticAt_of_spectralS_ne_zero {lam : ℝ} {z q : ℂ}
    (hS : spectralS z≠0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => transferW lam p.1 p.2) (z,q) := by
  unfold transferW spectralA spectralS spectralT
  have dz : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (z,q) := analyticAt_fst
  have dq : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (z,q) := analyticAt_snd
  exact (((Complex.analyticAt_cosh.comp dz).mul (Complex.analyticAt_cosh.comp (analyticAt_const.mul dz))).sub
    ((Complex.analyticAt_sinh.comp (analyticAt_const.mul dz)).mul (Complex.analyticAt_cos.comp dq))).div
    (Complex.analyticAt_sinh.comp dz) hS

theorem continuedTransferRoot_negative_joint_analyticAt {lam b : ℝ} {z : ℂ}
    (hS : spectralS z≠0) (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) (q : ℝ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => continuedTransferRoot lam p.1 p.2) (z,(q : ℂ)) := by
  have hW : transferW lam z (q : ℂ)∈continuedRootDomain := by
    rw [negative_transferW_eq_edgeW hS hedge]
    exact edgeW_domain hb hB _
  exact AnalyticAt.fun_comp_of_eq (f := fun p : ℂ × ℂ => transferW lam p.1 p.2)
    (g := continuedRoot) (continuedRoot_analyticAt hW)
    (transferW_joint_analyticAt_of_spectralS_ne_zero hS) rfl

theorem continuedTransferRoot_negative_pair_ne_zero {lam b : ℝ} {z : ℂ}
    (hS : spectralS z≠0) (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) (q t : ℝ) :
    1-continuedTransferRoot lam z (q : ℂ)*continuedTransferRoot lam z (t : ℂ)≠0 := by
  rw [continuedTransferRoot_eq_edgeRoot hS hedge, continuedTransferRoot_eq_edgeRoot hS hedge]
  exact edgeRoot_pair_denominator_ne_zero hb hB _ _

theorem continuedTransferRoot_odd_negative_product_lt_one {N : ℕ} (hN : Odd N)
    {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im)
    (q : Fin N → ℝ) (hq : ∑ i, q i=0) :
    ‖∏ i, continuedTransferRoot lam z (q i : ℂ)‖<1 := by
  simp_rw [continuedTransferRoot_eq_edgeRoot hS hedge]
  exact odd_negative_root_product_lt_one hN hb hB q hq

theorem continuedTransferRoot_eq_transferRoot_of_im_pos {lam : ℝ} {z q : ℂ}
    (hi : 0<(transferW lam z q).im) : continuedTransferRoot lam z q=transferRoot lam z q := by
  unfold continuedTransferRoot transferRoot
  rw [continuedRoot_eq_interiorRoot hi]
  exact (smallRoot_eq_of_quadratic (Or.inl (ne_of_gt hi))
    (interiorRoot_quadratic _) (interiorRoot_norm_lt_one hi)).symm

end
end IsingBulk.Anisotropic.NegativeDominance
