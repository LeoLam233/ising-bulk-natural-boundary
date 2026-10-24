import IsingBulk.Anisotropic.Geometry.AxisExchange
import IsingBulk.Anisotropic.Geometry.Components

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem omegaH_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaH lam) :
    (lam:ℂ)*z∈omegaH (lam⁻¹) := by
  have hc := (omegaH_isPreconnected hlam).image (fun w : ℂ => (lam:ℂ)*w)
    (continuous_const.mul continuous_id).continuousOn
  have h0 : (0:ℂ)∈(fun w : ℂ => (lam:ℂ)*w) '' omegaH lam :=
    ⟨0,zero_mem_omegaH hlam,by simp⟩
  have hs : (fun w : ℂ => (lam:ℂ)*w) '' omegaH lam⊆(spectralSet (lam⁻¹))ᶜ := by
    rintro _ ⟨w,hw,rfl⟩
    exact mt (mem_spectralSet_axis_exchange_iff hlam.ne' w).mp
      (omegaH_subset_spectral_complement hlam hw)
  have hh := hc.subset_connectedComponentIn h0 hs ⟨z,hz,rfl⟩
  simpa only [connectedComponentIn_spectral_complement_zero (inv_pos.mpr hlam)] using hh

theorem omegaH_axis_exchange_iff {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    (lam:ℂ)*z∈omegaH (lam⁻¹) ↔ z∈omegaH lam := by
  constructor
  · intro hz
    have hh := omegaH_axis_exchange (inv_pos.mpr hlam) hz
    simpa only [inv_inv,axis_exchange_scale hlam.ne'] using hh
  · exact omegaH_axis_exchange hlam

theorem omegaL_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaL lam) :
    (lam:ℂ)*z∈omegaL (lam⁻¹) := by
  let x := criticalPoint lam+1
  have hx : criticalPoint lam<x := by dsimp [x]; linarith
  have hx0 : 0<x := (criticalPoint_pos hlam).trans hx
  have hp := (criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hx
  have harg : lam⁻¹*(lam*x)=x := by field_simp
  have hx' : criticalPoint (lam⁻¹)<lam*x := by
    apply (criticalPoint_lt_iff_product_gt_one (inv_pos.mpr hlam) (mul_pos hlam hx0).le).mpr
    simpa only [harg,mul_comm] using hp
  have hc := (omegaL_isPreconnected hlam).image (fun w : ℂ => (lam:ℂ)*w)
    (continuous_const.mul continuous_id).continuousOn
  have h0 : ((lam*x:ℝ):ℂ)∈(fun w : ℂ => (lam:ℂ)*w) '' omegaL lam :=
    ⟨(x:ℂ),(real_mem_omegaL_iff hlam x).mpr hx,by push_cast; rfl⟩
  have hs : (fun w : ℂ => (lam:ℂ)*w) '' omegaL lam⊆(spectralSet (lam⁻¹))ᶜ := by
    rintro _ ⟨w,hw,rfl⟩
    exact mt (mem_spectralSet_axis_exchange_iff hlam.ne' w).mp
      (omegaL_subset_spectral_complement hlam hw)
  have hh := hc.subset_connectedComponentIn h0 hs ⟨z,hz,rfl⟩
  simpa only [connectedComponentIn_spectral_complement_supercritical (inv_pos.mpr hlam) hx'] using hh

theorem omegaL_axis_exchange_iff {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    (lam:ℂ)*z∈omegaL (lam⁻¹) ↔ z∈omegaL lam := by
  constructor
  · intro hz
    have hh := omegaL_axis_exchange (inv_pos.mpr hlam) hz
    simpa only [inv_inv,axis_exchange_scale hlam.ne'] using hh
  · exact omegaL_axis_exchange hlam

end
end IsingBulk.Anisotropic
