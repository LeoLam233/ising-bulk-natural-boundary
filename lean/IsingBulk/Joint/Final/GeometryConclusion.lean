import IsingBulk.Joint.Geometry.Components
import IsingBulk.Joint.Geometry.PhysicalExhaustion
import IsingBulk.Joint.Geometry.Modulus
import IsingBulk.Joint.Geometry.PrimeDensity
import IsingBulk.Joint.Geometry.PhysicalRegion
import IsingBulk.Joint.Slices.ExactDomains

namespace IsingBulk.Joint
noncomputable section
open Set

/-- The geometric clause uses literal independent-coupling domains and the
unsquared spectral set. It contains conclusions, not analytic input interfaces. -/
structure JointGeometryConclusion : Prop where
  high_component : connectedComponentIn spectralSetᶜ 0 = highDomain
  low_component : ∀ K ∈ lowDomain, connectedComponentIn spectralSetᶜ K = lowDomain
  high_real : ∀ x u : ℝ, 0 < x → 0 < u →
    (((x:ℂ),(u:ℂ)) ∈ highDomain ↔ Real.sinh x*Real.sinh u < 1)
  low_real : ∀ x u : ℝ, 0 < x → 0 < u →
    (((x:ℂ),(u:ℂ)) ∈ lowDomain ↔ 1 < Real.sinh x*Real.sinh u)
  high_contractible : ContractibleSpace highDomain
  low_contractible : ContractibleSpace lowDomain
  high_modulus : ∀ K ∈ highDomain, ‖p K‖ < 1
  low_modulus : ∀ K ∈ lowDomain, 1 < ‖p K‖
  high_psh : IsPlurisubharmonicOn paperSpectralExhaustion highDomain
  low_psh : IsPlurisubharmonicOn paperSpectralExhaustion lowDomain
  high_exhaustion : ∀ r : ℝ, IsCompact {K | K ∈ highDomain ∧ paperSpectralExhaustion K ≤ r}
  low_exhaustion : ∀ r : ℝ, IsCompact {K | K ∈ lowDomain ∧ paperSpectralExhaustion K ≤ r}
  high_pullback : ∀ lam : ℝ, 0 < lam → ratioSlice lam ⁻¹' highDomain = Anisotropic.omegaH lam
  low_pullback : ∀ lam : ℝ, 0 < lam → ratioSlice lam ⁻¹' lowDomain = Anisotropic.omegaL lam

theorem joint_geometry_conclusion : JointGeometryConclusion where
  high_component := highDomain_origin_component
  low_component := lowDomain_component
  high_real := fun _ _ hx hu => realPositive_mem_high_iff hx hu
  low_real := fun _ _ hx hu => realPositive_mem_low_iff hx hu
  high_contractible := highDomain_contractible
  low_contractible := lowDomain_contractible
  high_modulus := fun _ h => norm_p_lt_one h
  low_modulus := fun _ h => one_lt_norm_p h
  high_psh := (physical_components_paper_exhaustion (Or.inl rfl)).1
  low_psh := (physical_components_paper_exhaustion (Or.inr rfl)).1
  high_exhaustion := (physical_components_paper_exhaustion (Or.inl rfl)).2
  low_exhaustion := (physical_components_paper_exhaustion (Or.inr rfl)).2
  high_pullback := fun _ h => highDomain_pullback h
  low_pullback := fun _ h => lowDomain_pullback h

end
end IsingBulk.Joint
