import IsingBulk.Anisotropic.Geometry.AnalyticProfiles

namespace IsingBulk.Anisotropic
noncomputable section
open Filter
open scoped Topology

def openingLeftCurve (lam y : ℝ) : ℝ := slicePInv lam (Real.cos y)
def openingRightCurve (lam y : ℝ) : ℝ := sliceQInv lam (Real.cos (lam*y))
def openingMidpoint (lam y : ℝ) : ℂ :=
  (((openingLeftCurve lam y+openingRightCurve lam y)/2:ℝ):ℂ)+(y:ℂ)*Complex.I

theorem opening_midpoint_strict_signs {lam y : ℝ} (hlam : 0<lam)
    (hc : 0<Real.cos y) (hcl : 0<Real.cos (lam*y))
    (hne : openingLeftCurve lam y≠openingRightCurve lam y) :
    geometryF1 lam (openingMidpoint lam y).re (openingMidpoint lam y).im*
      geometryF2 lam (openingMidpoint lam y).re (openingMidpoint lam y).im<0 := by
  let a := openingLeftCurve lam y
  let b := openingRightCurve lam y
  have ha : 0<a := by simpa only [a,openingLeftCurve,slicePInv_zero hlam] using slicePInv_strictMono hlam hc
  have hb : 0<b := by simpa only [b,openingRightCurve,sliceQInv_zero hlam] using sliceQInv_strictMono hlam hcl
  have hm : 0≤(a+b)/2 := by positivity
  have hf1n := geometryF1_neg_iff hlam hm y
  have hf1p := geometryF1_pos_iff hlam hm y
  have hf2n := geometryF2_neg_iff hlam hm y
  have hf2p := geometryF2_pos_iff hlam hm y
  rw [abs_of_pos hc] at hf1n hf1p
  rw [abs_of_pos hcl] at hf2n hf2p
  simp only [openingMidpoint,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,add_zero,zero_add]
  change geometryF1 lam ((a+b)/2) y*geometryF2 lam ((a+b)/2) y<0
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact mul_neg_of_neg_of_pos (hf1n.mpr (by change a<(a+b)/2; change a<b at hab; linarith))
      (hf2p.mpr (by change (a+b)/2<b; change a<b at hab; linarith))
  · exact mul_neg_of_pos_of_neg (hf1p.mpr (by change (a+b)/2<a; change b<a at hab; linarith))
      (hf2n.mpr (by change b<(a+b)/2; change b<a at hab; linarith))

theorem mem_interior_spectralSet_of_strict_signs {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : geometryF1 lam z.re z.im*geometryF2 lam z.re z.im<0) :
    z∈interior (spectralSet lam) := by
  let V : Set ℂ := {w | geometryF1 lam w.re w.im*geometryF2 lam w.re w.im<0}
  have ho : IsOpen V := isOpen_lt ((geometryF1_continuous lam).mul
    (geometryF2_continuous lam)) continuous_const
  have hm : V⊆spectralSet lam := fun w hw => (mem_spectralSet_iff_signs hlam w).mpr hw.le
  exact (interior_mono hm) (by rw [ho.interior_eq]; exact hz)

theorem opening_midpoint_eventually_interior {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    ∀ᶠ y in 𝓝[≠] (0:ℝ), openingMidpoint lam y∈interior (spectralSet lam) := by
  have hc : ∀ᶠ y in 𝓝 (0:ℝ),0<Real.cos y :=
    continuousAt_const.eventually_lt Real.continuous_cos.continuousAt (by norm_num)
  have hcl : ∀ᶠ y in 𝓝 (0:ℝ),0<Real.cos (lam*y) :=
    continuousAt_const.eventually_lt
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt (by norm_num)
  filter_upwards [edgeIntersectionProfile_locally_nonzero hlam hne 0,
    hc.filter_mono nhdsWithin_le_nhds,hcl.filter_mono nhdsWithin_le_nhds] with y hy hc hcl
  apply mem_interior_spectralSet_of_strict_signs hlam
  apply opening_midpoint_strict_signs hlam hc hcl
  intro he
  apply hy
  unfold edgeIntersectionProfile
  change geometryF2 lam (openingLeftCurve lam y) y=0
  rw [he]
  simp only [openingRightCurve,geometryF2_factor,sliceQ_apply_inv hlam,sub_self,mul_zero]

/-- Every neighborhood of the actual critical point contains an open part of
the spectral set for every strictly anisotropic positive ratio. -/
theorem criticalPoint_mem_closure_interior_spectralSet {lam : ℝ}
    (hlam : 0<lam) (hne : lam≠1) :
    (criticalPoint lam:ℂ)∈closure (interior (spectralSet lam)) := by
  have h1 : Continuous (openingLeftCurve lam) :=
    (slicePInv_continuous hlam).comp Real.continuous_cos
  have h2 : Continuous (openingRightCurve lam) :=
    (sliceQInv_continuous hlam).comp (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hf : Continuous (openingMidpoint lam) :=
    (Complex.continuous_ofReal.comp ((h1.add h2).div_const 2)).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hzero : openingMidpoint lam 0=(criticalPoint lam:ℂ) := by
    simp [openingMidpoint,openingLeftCurve,openingRightCurve,sliceQInv_one hlam,criticalPoint]
  have hlim : Tendsto (openingMidpoint lam) (𝓝[≠] (0:ℝ)) (𝓝 (criticalPoint lam:ℂ)) := by
    rw [←hzero]
    exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim (opening_midpoint_eventually_interior hlam hne)

theorem anisotropic_spectral_interior_arbitrarily_close {lam : ℝ}
    (hlam : 0<lam) (hne : lam≠1) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃z∈interior (spectralSet lam),dist z (criticalPoint lam:ℂ)<epsilon := by
  obtain ⟨z,hz,hd⟩ := Metric.mem_closure_iff.mp
    (criticalPoint_mem_closure_interior_spectralSet hlam hne) epsilon hepsilon
  exact ⟨z,hz,by simpa only [dist_comm] using hd⟩

end
end IsingBulk.Anisotropic
