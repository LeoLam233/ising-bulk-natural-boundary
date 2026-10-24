import IsingBulk.Anisotropic.Geometry.RealEdgeSides
import IsingBulk.Anisotropic.Geometry.LocalFrontierChart

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology
open Set Filter Metric

theorem edgeMapU_at_endpoint {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (hu : spectralU lam z=e) :
    edgeMapU lam (e:ℂ) z=(spectralV lam z:ℂ) := by
  unfold edgeMapU
  rw [div_eq_iff (spectralT_ne_zero_of_det_ne_zero hd)]
  rw [spectral_reconstruction hd,hu]
  ring

theorem edgeMapV_at_endpoint {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (hv : spectralV lam z=e) :
    edgeMapV lam (e:ℂ) z=(spectralU lam z:ℂ) := by
  unfold edgeMapV
  rw [div_eq_iff (spectralS_ne_zero_of_det_ne_zero hd)]
  rw [spectral_reconstruction hd,hv]
  ring

/-- At an actual regular U-endpoint, the entire real diameter of the inverse chart
stays on the frontier of the original, specified complement component. -/
theorem actual_U_same_component_frontier_chart {lam : ℝ} {z : ℂ} (a : ℂ) {e : ℝ}
    (hz : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a))
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hu : spectralU lam z=e)
    (hv : |spectralV lam z|<1) (hder : deriv (edgeMapU lam (e:ℂ)) z≠0) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      (E:ℂ→ℂ)=(fun w => ((-e*spectralDet lam z:ℝ):ℂ)*edgeMapU lam (e:ℂ) w) ∧
      z∈E.source ∧ ∃ r>0, ball (E z) r⊆E.target ∧
      ∀ w∈ball (E z) r, w.im=0 → E.symm w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) := by
  have ha := edgeMapU_analyticAt (e := (e:ℂ)) (spectralT_ne_zero_of_det_ne_zero hd)
  have hc : ((-e*spectralDet lam z:ℝ):ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (neg_ne_zero.mpr (by rcases he with rfl | rfl <;> norm_num)) hd
  have hf := ha.differentiableAt.hasDerivAt.const_mul (((-e*spectralDet lam z:ℝ):ℂ))
  obtain ⟨E,hE,hzE,r,hr,hrE,hfront⟩ := exists_same_component_frontier_chart
    (spectralSet_isClosed lam) a hz (analyticAt_const.mul ha)
    (hf.deriv ▸ mul_ne_zero hc hder) (actual_U_edge_halfplane hd he hu hv)
  exact ⟨E,hE,hzE,r,hr,by simpa only [hE] using hrE,by simpa only [hE] using hfront⟩

theorem actual_V_same_component_frontier_chart {lam : ℝ} {z : ℂ} (a : ℂ) {e : ℝ}
    (hz : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a))
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hv : spectralV lam z=e)
    (hu : |spectralU lam z|<1) (hder : deriv (edgeMapV lam (e:ℂ)) z≠0) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      (E:ℂ→ℂ)=(fun w => ((e*spectralDet lam z:ℝ):ℂ)*edgeMapV lam (e:ℂ) w) ∧
      z∈E.source ∧ ∃ r>0, ball (E z) r⊆E.target ∧
      ∀ w∈ball (E z) r, w.im=0 → E.symm w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) := by
  have ha := edgeMapV_analyticAt (lam := lam) (e := (e:ℂ)) (spectralS_ne_zero_of_det_ne_zero hd)
  have hc : ((e*spectralDet lam z:ℝ):ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (by rcases he with rfl | rfl <;> norm_num) hd
  have hf := ha.differentiableAt.hasDerivAt.const_mul (((e*spectralDet lam z:ℝ):ℂ))
  obtain ⟨E,hE,hzE,r,hr,hrE,hfront⟩ := exists_same_component_frontier_chart
    (spectralSet_isClosed lam) a hz (analyticAt_const.mul ha)
    (hf.deriv ▸ mul_ne_zero hc hder) (actual_V_edge_halfplane hd he hv hu)
  exact ⟨E,hE,hzE,r,hr,by simpa only [hE] using hrE,by simpa only [hE] using hfront⟩

end
end IsingBulk.Anisotropic
