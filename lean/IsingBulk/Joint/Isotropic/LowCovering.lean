import IsingBulk.Joint.Isotropic.ExteriorHomeomorph
import IsingBulk.Anisotropic.Geometry.LowTopology

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

theorem exp_preimage_outerRootDomain :
    Complex.exp ⁻¹' outerRootDomain = omegaL 1 := by
  ext z
  change (1 < ‖Complex.exp z‖ ∧ 1 < ‖sinhJoukowski (Complex.exp z)‖) ↔ _
  rw [Complex.norm_exp, Real.one_lt_exp_iff, ← sinh_eq_joukowski_exp, mem_omegaL_one_iff]

/-- The actual restricted exponential, on its exact geometric preimage. -/
def lowExpMap : omegaL 1 → outerRootDomain := fun z =>
  ⟨Complex.exp z, by
    change z.val ∈ Complex.exp ⁻¹' outerRootDomain
    rw [exp_preimage_outerRootDomain]
    exact z.property⟩

theorem lowExpMap_isCoveringMap : IsCoveringMap lowExpMap := by
  have hsub : outerRootDomain ⊆ ({0} : Set ℂ)ᶜ := by
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    norm_num [outerRootDomain,h] at hv
  have he := (Complex.isCoveringMapOn_exp.mono hsub).isCoveringMap_restrictPreimage
  convert he.comp_homeomorph (Homeomorph.setCongr exp_preimage_outerRootDomain.symm) using 1
  funext z
  rfl

/-- The literal sinh map to the full exterior. -/
def lowSinhMap : omegaL 1 → exteriorDisk := fun z =>
  ⟨Complex.sinh z, ((mem_omegaL_one_iff z).mp z.property).2⟩

theorem lowSinhMap_isCoveringMap : IsCoveringMap lowSinhMap := by
  convert lowExpMap_isCoveringMap.homeomorph_comp exteriorRootHomeomorph using 1
  funext z
  apply Subtype.ext
  exact sinh_eq_joukowski_exp z

/-- Universal covering: the exact sinh map is a covering and its entire source
cell is simply connected. Exact fibers/deck translations are `sinh_fiber_low`. -/
theorem low_universal_covering :
    IsCoveringMap lowSinhMap ∧ IsSimplyConnected (omegaL 1) :=
  ⟨lowSinhMap_isCoveringMap, omegaL_isSimplyConnected (by norm_num)⟩

end
end IsingBulk.Joint
