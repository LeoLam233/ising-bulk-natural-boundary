import IsingBulk.Tail.SelectorOrderSplit
import IsingBulk.Tail.SelectedBranchData

/-! The genuine original damping domain at the fixed source radial radius.
This is uniform in particle number and every fixed derivative order. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

theorem radial_source_eventually_damping (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∀ᶠ eps : ℝ in 𝓝[>] 0,
      0 < Real.exp (-d.c₀*eps) ∧ Real.exp (-d.c₀*eps) < 1 ∧
      radialParameter d.theta eps ∈ dampingDomain (Real.exp (-d.c₀*eps)) := by
  have hsin : 0 < Real.sin d.theta :=
    Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by have := d.theta_lt; linarith [Real.pi_pos])
  obtain ⟨e,he,_,hm⟩ := radialDampingMargin_linear hsin hcsmall
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < e from
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))] with eps heps hsmall
  have hp : 0 < eps := heps
  have hr : Real.exp (-d.c₀*eps)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  refine ⟨Real.exp_pos _,hr,?_,?_⟩
  · apply norm_ne_zero_iff.mp
    rw [radialParameter_norm hp.le]
    linarith
  · have hh := radialRadius_parameter_margin hp (hm eps hp hsmall)
    linarith [mul_pos hsin hp]

end
end IsingBulk.Tail
