import IsingBulk.Preferred22.SelectedOneBody

/-! The explicit continuation of the sheet selected by the physical root at
a base dispersion point. It is not replaced by the globally chosen interior
root when a regular coordinate crosses the dispersion cut. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set Complex
open scoped Topology
set_option maxHeartbeats 800000

theorem preferred_local_root_germ {W : ℂ} (hW : OffRealSegment W) :
    localPhysicalRoot W =ᶠ[𝓝 W] physicalRoot := by
  have hD := offRealSegment_discriminant_ne_zero hW
  have hc := (localPhysicalRoot_analyticAt hD).continuousAt
  have hn : ‖localPhysicalRoot W W‖<1 := by
    rw [localPhysicalRoot_at hD]
    exact physicalRoot_inside hW
  have he := hc.norm.eventually_lt continuousAt_const hn
  filter_upwards [he,isOpen_offRealSegment.eventually_mem hW] with V hV hoff
  exact root_unique_in_disk (localPhysicalRoot_trace hD V) (physicalRoot_trace V)
    (localPhysicalRoot_ne_zero hD V) (physicalRoot_ne_zero V) hV (physicalRoot_inside hoff)

theorem preferred_local_root_analyticAt {W V : ℂ}
    (hslit : (V^2-1)/(W^2-1)∈slitPlane) :
    AnalyticAt ℂ (localPhysicalRoot W) V := by
  have hg : AnalyticAt ℂ (fun Z : ℂ => (Z^2-1)/(W^2-1)) V :=
    ((analyticAt_id.pow 2).sub analyticAt_const).div_const
  have hs : AnalyticAt ℂ (fun Z : ℂ => Complex.sqrt ((Z^2-1)/(W^2-1))) V :=
    hg.cpow analyticAt_const hslit
  exact analyticAt_id.add (analyticAt_const.mul hs)

/-- Quantitative legal sheet disk, stated in the dispersion variable. -/
theorem preferred_discriminant_ratio_disk {W V : ℂ} {R : ℝ}
    (hR : 0≤R) (hW : ‖W‖≤R) (hD : W^2-1≠0)
    (hsmall : ‖V-W‖≤1)
    (hdelta : ‖V-W‖≤‖W^2-1‖/(2*(2*R+1))) :
    ‖(V^2-1)/(W^2-1)-1‖≤1/2 ∧
    1/2≤((V^2-1)/(W^2-1)).re ∧
    ‖W^2-1‖/2≤‖V^2-1‖ ∧
    AnalyticAt ℂ (localPhysicalRoot W) V := by
  have hden : 0<‖W^2-1‖ := norm_pos_iff.mpr hD
  have hR1 : 0<2*R+1 := by positivity
  have hp : ‖V+W‖≤2*R+1 := by
    have he : V+W=(V-W)+2*W := by ring
    rw [he]
    have h := norm_add_le (V-W) (2*W)
    rw [norm_mul,Complex.norm_ofNat] at h
    linarith
  have he : (V^2-1)/(W^2-1)-1=(V-W)*(V+W)/(W^2-1) := by
    field_simp
    ring
  have hratio : ‖(V^2-1)/(W^2-1)-1‖≤1/2 := by
    rw [he,norm_div,norm_mul]
    apply (div_le_iff₀ hden).mpr
    have hd := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hR1)).mp hdelta
    have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (V-W))
    nlinarith
  have hre : 1/2≤((V^2-1)/(W^2-1)).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm ((V^2-1)/(W^2-1)-1))).1
    simp only [Complex.sub_re,Complex.one_re] at h
    linarith
  have hdisc : ‖W^2-1‖/2≤‖V^2-1‖ := by
    have hnorm : 1/2≤‖(V^2-1)/(W^2-1)‖ := hre.trans (Complex.re_le_norm _)
    rw [norm_div] at hnorm
    have h := (le_div_iff₀ hden).mp hnorm
    linarith
  refine ⟨hratio,hre,hdisc,preferred_local_root_analyticAt (Or.inl ?_)⟩
  linarith

end
end IsingBulk.Preferred22
