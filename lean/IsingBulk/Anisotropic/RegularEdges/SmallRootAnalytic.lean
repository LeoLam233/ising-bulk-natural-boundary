import IsingBulk.Anisotropic.RegularEdges.SmallRoot

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology

def joukowski (z : ℂ) : ℂ := (z+z⁻¹)/2

theorem joukowski_hasDerivAt {z : ℂ} (hz : z≠0) :
    HasDerivAt joukowski ((1-(z^2)⁻¹)/2) z := by
  convert ((hasDerivAt_id z).add ((hasDerivAt_id z).inv hz)).div_const 2 using 1
  · rfl
  · simp [div_eq_mul_inv,sub_eq_add_neg]

theorem joukowski_deriv_ne_zero {z : ℂ} (hz : z≠0) (hn : ‖z‖<1) : deriv joukowski z≠0 := by
  rw [(joukowski_hasDerivAt hz).deriv]
  intro he
  have hh : z^2=1 := by
    have h1 := (div_eq_zero_iff.mp he).resolve_right (by norm_num : (2:ℂ)≠0)
    have h2 : (z^2)⁻¹=1 := (sub_eq_zero.mp h1).symm
    simpa only [inv_eq_one] using h2
  have hnorm := congrArg norm hh
  rw [norm_pow,norm_one] at hnorm
  nlinarith [norm_nonneg z]

/-- Holomorphy is obtained from the actual Joukowski inverse and uniqueness
inside the disk, not from continuity of an arbitrary choice function. -/
theorem smallRoot_analyticAt {W : ℂ} (hW : W∈SmallRootDomain) : AnalyticAt ℂ smallRoot W := by
  let z := smallRoot W
  have hz : z≠0 := smallRoot_ne_zero hW
  have hn : ‖z‖<1 := (smallRoot_spec hW).2
  have hj : joukowski z=W := by
    have hh := quadratic_root_trace (smallRoot_spec hW).1
    dsimp [joukowski,z]
    rw [hh]
    ring
  have ha : AnalyticAt ℂ joukowski z :=
    (analyticAt_id.add (analyticAt_id.inv hz)).div_const
  obtain ⟨ψ,hψ,hψ0,hr,_hl⟩ := exists_analytic_local_inverse ha (joukowski_deriv_ne_zero hz hn)
  rw [hj] at hψ hψ0 hr
  have hnorm : ∀ᶠ w in 𝓝 W, ‖ψ w‖<1 :=
    hψ.continuousAt.norm.eventually_lt_const (by change ‖ψ W‖<1; rw [hψ0]; exact hn)
  have hne : ∀ᶠ w in 𝓝 W, ψ w≠0 := hψ.continuousAt.eventually_ne (by rw [hψ0]; exact hz)
  apply hψ.congr
  filter_upwards [hr,hnorm,hne,smallRootDomain_isOpen.mem_nhds hW] with w hw hwn hw0 hwd
  apply (smallRoot_eq_of_quadratic hwd _ hwn).symm
  unfold joukowski at hw
  field_simp [hw0] at hw
  linear_combination hw

end
end IsingBulk.Anisotropic.RegularEdges
