import IsingBulk.Anisotropic.NegativeDominance.ComponentHalfplaneInverse
import IsingBulk.Anisotropic.Geometry.Components

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter
open scoped Topology

theorem negative_ratio_im (lam : ℝ) (z : ℂ) :
    (-spectralT lam z/spectralS z).im=
      -spectralDet lam z/Complex.normSq (spectralS z) := by
  simp only [Complex.div_im,Complex.neg_re,Complex.neg_im,spectralDet]
  ring

theorem negative_ratio_im_pos {lam : ℝ} {z : ℂ} (hd : spectralDet lam z<0) :
    0<(-spectralT lam z/spectralS z).im := by
  rw [negative_ratio_im]
  exact div_pos (neg_pos.mpr hd) (Complex.normSq_pos.mpr
    (spectralS_ne_zero_of_det_ne_zero hd.ne))

/-- The actual nonramified negative V-endpoint chart, with its entire upper
half-disk proved to map into the original HT component. Orientation is fixed
by the sign of the actual spectral determinant. -/
theorem exists_negative_physical_chart {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) :
    ∃ zeta : ℂ → ℂ, AnalyticAt ℂ zeta 0 ∧ zeta 0=z ∧
      ∃ r : ℝ, 0<r ∧ ∀ u : ℂ, ‖u‖<r →
        edgeMapV lam (-1) (zeta u)=(spectralU lam z : ℂ)+u ∧
        (0<u.im → zeta u∈omegaH lam) := by
  let f : ℂ → ℂ := fun w => edgeMapV lam (-1) w-(spectralU lam z : ℂ)
  have ha := edgeMapV_analyticAt (lam := lam) (e := (-1 : ℂ))
    (spectralS_ne_zero_of_det_ne_zero hd.ne)
  have hf : AnalyticAt ℂ f z := ha.sub analyticAt_const
  have hfz : f z=0 := by
    dsimp [f]
    have hm := edgeMapV_at_endpoint hd.ne hv
    norm_num only [Complex.ofReal_neg,Complex.ofReal_one] at hm
    rw [hm,sub_self]
  have hfd : deriv f z≠0 := by
    simpa only [f,deriv_sub_const] using hder
  have hside : ∀ᶠ w in 𝓝 z, w∈spectralSet lam ↔ (f w).im≤0 := by
    filter_upwards [actual_V_edge_halfplane hd.ne (Or.inr rfl) hv hu] with w hw
    simp only [Complex.ofReal_neg,Complex.ofReal_one] at hw
    rw [hw]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      neg_mul,one_mul,f,Complex.sub_im,sub_zero]
    constructor <;> intro h <;> nlinarith
  have hfront : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ 0) := by
    simpa only [connectedComponentIn_spectral_complement_zero hlam] using hz
  obtain ⟨zeta,hza,hz0,r,hr,hzeta⟩ := exists_component_halfplane_inverse
    (spectralSet_isClosed lam) 0 hfront hf hfz hfd hside
  refine ⟨zeta,hza,hz0,r,hr,?_⟩
  intro u hurn
  obtain ⟨hf,hin⟩ := hzeta u hurn
  refine ⟨?_,?_⟩
  · dsimp [f] at hf
    exact sub_eq_iff_eq_add'.mp hf
  · simpa only [connectedComponentIn_spectral_complement_zero hlam] using hin

end
end IsingBulk.Anisotropic.NegativeDominance
