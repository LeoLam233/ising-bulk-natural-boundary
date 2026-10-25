import IsingBulk.Joint.Geometry.HighRegularDensity
import IsingBulk.Joint.Transverse.TransferFace

namespace IsingBulk.Joint
noncomputable section
open Set

theorem transferB_im_ne_of_regular {K : Coupling} (hK : IsRegularJointEdge K) :
    (transferB K).im ≠ 0 := by
  have hd : spectralDet K ≠ 0 := by
    simpa only [spectralDet,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      neg_mul,sub_eq_add_neg] using hK.2.2.2.1
  have he : (transferB K).im = spectralDet K / Complex.normSq (S K) := by
    simp only [transferB,Complex.div_im,spectralDet]
    ring
  rw [he]
  exact div_ne_zero hd ((Complex.normSq_pos.mpr hK.2.1).ne')

theorem regularJointEdge_of_transfer {K : Coupling} {b eps : ℝ}
    (hboundary : K ∈ frontier highDomain ∪ frontier lowDomain)
    (hS : S K ≠ 0) (hB : (transferB K).im ≠ 0) (hp : p K^2 ≠ 1)
    (hb : |b| < 1) (heps : eps = -1 ∨ eps = 1)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) : IsRegularJointEdge K := by
  have hT : T K ≠ 0 := by
    intro h
    apply hB
    simp [transferB,h]
  have hd : (star (S K)*T K).im ≠ 0 := by
    intro h
    apply hB
    have he' : (transferB K).im = (star (S K)*T K).im / Complex.normSq (S K) := by
      simp only [transferB,Complex.div_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
      ring
    rw [he',h,zero_div]
  have heq : A K = S K*(b:ℂ)+T K*(eps:ℂ) := by
    unfold transferC transferB at he
    field_simp at he
    linear_combination he
  have hepsbound : eps ∈ Icc (-1:ℝ) 1 := by rcases heps with h | h <;> simp [h]
  exact ⟨hboundary,hS,hT,hd,hp,b,abs_le.mp hb.le,eps,hepsbound,heq,
    Or.inr ⟨abs_lt.mp hb,heps⟩⟩

end
end IsingBulk.Joint
