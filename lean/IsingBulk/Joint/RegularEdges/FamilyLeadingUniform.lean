import IsingBulk.Joint.Negative.CompactFamilies
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Compactness upgrades genuinely joint one-sided limits to one uniform
radius. This theorem does not confuse separate pointwise limits with uniform
convergence. -/
theorem compact_joint_limit_uniform {E : Type*} [NormedAddCommGroup E]
    {Q : Set E} (hQ : IsCompact Q) {F : ℝ × E → ℂ} {L : E → ℂ}
    (hL : ContinuousOn L Q)
    (hlim : ∀eta∈Q,Tendsto F (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta)) (𝓝 (L eta))) :
    ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ‖F (t,eta)-L eta‖<ε := by
  intro ε hε
  let U : Set (ℝ × E) := interior {p | p∈Ioi (0:ℝ) ×ˢ Q → ‖F p-L p.2‖<ε}
  have hcenter (eta : E) (heta : eta∈Q) : (0,eta)∈U := by
    have he : Tendsto (fun p : ℝ × E => p.2)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta)) (𝓝[Q] eta) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact hp.2
    have hh : Tendsto (fun p : ℝ × E => F p-L p.2)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta)) (𝓝 0) := by
      simpa using! (hlim eta heta).sub ((hL eta heta).tendsto.comp he)
    have hev : ∀ᶠ p in 𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta), ‖F p-L p.2‖<ε :=
      (hh.norm).eventually (eventually_lt_nhds (by simpa using hε))
    exact mem_interior_iff_mem_nhds.mpr (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨δ,hδ,htube⟩ := Negative.compact_product_tube hQ isOpen_interior hcenter
  refine ⟨δ,hδ,?_⟩
  intro eta heta t ht htδ
  have hh := interior_subset (htube eta heta t (by simpa only [Real.norm_eq_abs,abs_of_pos ht] using htδ))
  exact hh ⟨ht,heta⟩

end
end IsingBulk.Joint.RegularEdges
