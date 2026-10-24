import IsingBulk.Anisotropic.Geometry.Definitions
import IsingBulk.Anisotropic.Geometry.SpectralAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

theorem axis_exchange_scale {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    ((lam⁻¹:ℝ):ℂ)*((lam:ℂ)*z)=z := by
  have h : (lam:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hlam
  simp only [Complex.ofReal_inv,← mul_assoc,inv_mul_cancel₀ h,one_mul]

theorem spectralT_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralT (lam⁻¹) ((lam:ℂ)*z)=spectralS z := by
  simp only [spectralT,spectralS,axis_exchange_scale hlam]

theorem spectralA_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralA (lam⁻¹) ((lam:ℂ)*z)=spectralA lam z := by
  simp only [spectralA,axis_exchange_scale hlam]
  ring

theorem spectralProduct_axis_exchange {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    spectralProduct (lam⁻¹) ((lam:ℂ)*z)=spectralProduct lam z := by
  unfold spectralProduct
  rw [spectralT_axis_exchange hlam]
  unfold spectralS spectralT
  ring

theorem mem_spectralSet_axis_exchange_iff {lam : ℝ} (hlam : lam≠0) (z : ℂ) :
    (lam:ℂ)*z∈spectralSet (lam⁻¹) ↔ z∈spectralSet lam := by
  constructor
  · rintro ⟨u,hu,v,hv,he⟩
    refine ⟨v,hv,u,hu,?_⟩
    rw [spectralA_axis_exchange hlam,spectralT_axis_exchange hlam] at he
    simpa only [spectralS,spectralT,add_comm] using he
  · rintro ⟨u,hu,v,hv,he⟩
    refine ⟨v,hv,u,hu,?_⟩
    rw [spectralA_axis_exchange hlam,spectralT_axis_exchange hlam]
    simpa only [spectralS,spectralT,add_comm] using he

end
end IsingBulk.Anisotropic
