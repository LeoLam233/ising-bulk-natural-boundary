import IsingBulk.Anisotropic.NegativeDominance.ComponentHalfplaneInverse
import IsingBulk.Anisotropic.Geometry.Components

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

theorem exists_oriented_V_component_chart (lam : ℝ) (a : ℂ) {z : ℂ} {e : ℝ}
    (hz : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a))
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hv : spectralV lam z=e)
    (hu : |spectralU lam z|<1) (hder : deriv (edgeMapV lam (e:ℂ)) z≠0)
    (horient : 0<e*spectralDet lam z) :
    ∃ zeta : ℂ → ℂ, AnalyticAt ℂ zeta 0 ∧ zeta 0=z ∧
      ∃ r : ℝ, 0<r ∧ ∀ u : ℂ, ‖u‖<r →
        edgeMapV lam (e:ℂ) (zeta u)=(spectralU lam z:ℂ)+u ∧
        (0<u.im → zeta u∈connectedComponentIn (spectralSet lam)ᶜ a) := by
  let f : ℂ → ℂ := fun w => edgeMapV lam (e:ℂ) w-(spectralU lam z:ℂ)
  have ha := edgeMapV_analyticAt (lam := lam) (e := (e:ℂ)) (spectralS_ne_zero_of_det_ne_zero hd)
  have hf : AnalyticAt ℂ f z := ha.sub analyticAt_const
  have hfz : f z=0 := by dsimp [f]; rw [edgeMapV_at_endpoint hd hv,sub_self]
  have hfd : deriv f z≠0 := by simpa only [f,deriv_sub_const] using hder
  have hside : ∀ᶠ w in 𝓝 z, w∈spectralSet lam ↔ (f w).im≤0 := by
    filter_upwards [actual_V_edge_halfplane hd he hv hu] with w hw
    rw [hw]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      f,Complex.sub_im,sub_zero]
    constructor
    · intro h; nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos horient.le
  obtain ⟨zeta,hza,hz0,r,hr,hzeta⟩ := NegativeDominance.exists_component_halfplane_inverse
    (spectralSet_isClosed lam) a hz hf hfz hfd hside
  refine ⟨zeta,hza,hz0,r,hr,?_⟩
  intro u hu
  obtain ⟨hf,hin⟩ := hzeta u hu
  exact ⟨sub_eq_iff_eq_add'.mp hf,hin⟩

theorem exists_oriented_V_high_chart {lam : ℝ} (hlam : 0<lam) {z : ℂ} {e : ℝ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z≠0)
    (he : e=1 ∨ e= -1) (hv : spectralV lam z=e) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (e:ℂ)) z≠0) (horient : 0<e*spectralDet lam z) :
    ∃ zeta : ℂ → ℂ, AnalyticAt ℂ zeta 0 ∧ zeta 0=z ∧
      ∃ r : ℝ, 0<r ∧ ∀ u : ℂ, ‖u‖<r →
        edgeMapV lam (e:ℂ) (zeta u)=(spectralU lam z:ℂ)+u ∧
        (0<u.im → zeta u∈omegaH lam) := by
  simpa only [connectedComponentIn_spectral_complement_zero hlam] using
    exists_oriented_V_component_chart lam 0
      (by simpa only [connectedComponentIn_spectral_complement_zero hlam] using hz)
      hd he hv hu hder horient

theorem exists_oriented_V_low_chart {lam : ℝ} (hlam : 0<lam) {z : ℂ} {e : ℝ}
    (hz : z∈frontier (omegaL lam)) (hd : spectralDet lam z≠0)
    (he : e=1 ∨ e= -1) (hv : spectralV lam z=e) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (e:ℂ)) z≠0) (horient : 0<e*spectralDet lam z) :
    ∃ zeta : ℂ → ℂ, AnalyticAt ℂ zeta 0 ∧ zeta 0=z ∧
      ∃ r : ℝ, 0<r ∧ ∀ u : ℂ, ‖u‖<r →
        edgeMapV lam (e:ℂ) (zeta u)=(spectralU lam z:ℂ)+u ∧
        (0<u.im → zeta u∈omegaL lam) := by
  let x := criticalPoint lam+1
  have hx : criticalPoint lam<x := by dsimp [x]; linarith
  simpa only [connectedComponentIn_spectral_complement_supercritical hlam hx] using
    exists_oriented_V_component_chart lam (x:ℂ)
      (by simpa only [connectedComponentIn_spectral_complement_supercritical hlam hx] using hz)
      hd he hv hu hder horient

end
end IsingBulk.Anisotropic
