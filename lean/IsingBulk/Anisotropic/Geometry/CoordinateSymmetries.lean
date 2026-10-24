import IsingBulk.Anisotropic.Geometry.AxisExchange
import IsingBulk.Anisotropic.Geometry.RegularEdges
import Mathlib.Analysis.Calculus.Deriv.Star

namespace IsingBulk.Anisotropic
noncomputable section

theorem spectralS_conj (z : ℂ) : spectralS (star z)=star (spectralS z) := by
  exact Complex.sinh_conj z

theorem spectralT_conj (lam : ℝ) (z : ℂ) : spectralT lam (star z)=star (spectralT lam z) := by
  unfold spectralT
  rw [show (lam:ℂ)*star z=star ((lam:ℂ)*z) by simp]
  simp only [Complex.star_def,Complex.sinh_conj]

theorem spectralA_conj (lam : ℝ) (z : ℂ) : spectralA lam (star z)=star (spectralA lam z) := by
  unfold spectralA
  rw [show (lam:ℂ)*star z=star ((lam:ℂ)*z) by simp]
  rw [show Complex.cosh (star z)=star (Complex.cosh z) from Complex.cosh_conj z,
    show Complex.cosh (star ((lam:ℂ)*z))=star (Complex.cosh ((lam:ℂ)*z)) from Complex.cosh_conj _]
  exact (map_mul (starRingEnd ℂ) _ _).symm

theorem spectralDet_conj (lam : ℝ) (z : ℂ) : spectralDet lam (star z)= -spectralDet lam z := by
  unfold spectralDet
  rw [spectralS_conj,spectralT_conj]
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralNU_conj (lam : ℝ) (z : ℂ) : spectralNU lam (star z)= -spectralNU lam z := by
  unfold spectralNU
  rw [spectralA_conj,spectralT_conj]
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralNV_conj (lam : ℝ) (z : ℂ) : spectralNV lam (star z)= -spectralNV lam z := by
  unfold spectralNV
  rw [spectralS_conj,spectralA_conj]
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralU_conj (lam : ℝ) (z : ℂ) : spectralU lam (star z)=spectralU lam z := by
  simp only [spectralU,spectralNU_conj,spectralDet_conj,neg_div,div_neg,neg_neg]

theorem spectralV_conj (lam : ℝ) (z : ℂ) : spectralV lam (star z)=spectralV lam z := by
  simp only [spectralV,spectralNV_conj,spectralDet_conj,neg_div,div_neg,neg_neg]

theorem spectralS_axis_exchange (lam : ℝ) (z : ℂ) : spectralS ((lam:ℂ)*z)=spectralT lam z := rfl

theorem spectralDet_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralDet (lam⁻¹) ((lam:ℂ)*z)= -spectralDet lam z := by
  simp only [spectralDet,spectralS_axis_exchange,spectralT_axis_exchange hlam]
  ring

theorem spectralNU_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralNU (lam⁻¹) ((lam:ℂ)*z)= -spectralNV lam z := by
  simp only [spectralNU,spectralNV,spectralA_axis_exchange hlam,spectralT_axis_exchange hlam]
  ring

theorem spectralNV_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralNV (lam⁻¹) ((lam:ℂ)*z)= -spectralNU lam z := by
  simp only [spectralNU,spectralNV,spectralA_axis_exchange hlam,spectralS_axis_exchange]
  ring

theorem spectralU_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralU (lam⁻¹) ((lam:ℂ)*z)=spectralV lam z := by
  simp only [spectralU,spectralV,spectralNU_axis_exchange hlam,spectralDet_axis_exchange hlam,neg_div,div_neg,neg_neg]

theorem spectralV_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralV (lam⁻¹) ((lam:ℂ)*z)=spectralU lam z := by
  simp only [spectralU,spectralV,spectralNV_axis_exchange hlam,spectralDet_axis_exchange hlam,neg_div,div_neg,neg_neg]

theorem edgeMapU_conj (lam e : ℝ) (z : ℂ) : edgeMapU lam (e:ℂ) (star z)=star (edgeMapU lam (e:ℂ) z) := by
  unfold edgeMapU
  rw [spectralA_conj,spectralS_conj,spectralT_conj]
  simp only [Complex.star_def,map_div₀,map_sub,map_mul,Complex.conj_ofReal]

theorem edgeMapV_conj (lam e : ℝ) (z : ℂ) : edgeMapV lam (e:ℂ) (star z)=star (edgeMapV lam (e:ℂ) z) := by
  unfold edgeMapV
  rw [spectralA_conj,spectralS_conj,spectralT_conj]
  simp only [Complex.star_def,map_div₀,map_sub,map_mul,Complex.conj_ofReal]

theorem edgeMapU_axis_exchange {lam : ℝ} (hlam : lam≠0) (e z : ℂ) :
    edgeMapU (lam⁻¹) e ((lam:ℂ)*z)=edgeMapV lam e z := by
  simp only [edgeMapU,edgeMapV,spectralA_axis_exchange hlam,spectralT_axis_exchange hlam,spectralS_axis_exchange]

theorem edgeMapV_axis_exchange {lam : ℝ} (hlam : lam≠0) (e z : ℂ) :
    edgeMapV (lam⁻¹) e ((lam:ℂ)*z)=edgeMapU lam e z := by
  simp only [edgeMapU,edgeMapV,spectralA_axis_exchange hlam,spectralT_axis_exchange hlam,spectralS_axis_exchange]

end
end IsingBulk.Anisotropic
