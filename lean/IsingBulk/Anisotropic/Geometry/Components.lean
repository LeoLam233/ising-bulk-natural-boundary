import IsingBulk.Anisotropic.Geometry.BoundarySpectral
import IsingBulk.Anisotropic.Geometry.LowTopology
import IsingBulk.Anisotropic.Geometry.PhysicalAxis

namespace IsingBulk.Anisotropic
noncomputable section

theorem component_eq_of_frontier_subset {s f : Set ℂ} (ho : IsOpen s) (hc : IsPreconnected s)
    (hs : s⊆fᶜ) (hb : frontier s⊆f) {a : ℂ} (ha : a∈s) :
    connectedComponentIn fᶜ a=s := by
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset ho
    · exact ⟨a,mem_connectedComponentIn (hs ha),ha⟩
    · rintro z ⟨hz,hcomp⟩
      by_contra hn
      have hf : z∈frontier s := by rw [ho.frontier_eq]; exact ⟨hz,hn⟩
      exact (connectedComponentIn_subset fᶜ a hcomp) (hb hf)
  · exact hc.subset_connectedComponentIn ha hs

theorem omegaH_isPreconnected {lam : ℝ} (hlam : 0<lam) : IsPreconnected (omegaH lam) := by
  let : SimplyConnectedSpace (omegaH lam) := omegaH_isSimplyConnected hlam
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

theorem omegaL_isPreconnected {lam : ℝ} (hlam : 0<lam) : IsPreconnected (omegaL lam) := by
  let : SimplyConnectedSpace (omegaL lam) := omegaL_isSimplyConnected hlam
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- The physical HT domain is exactly the spectral-complement component containing zero. -/
theorem connectedComponentIn_spectral_complement_zero {lam : ℝ} (hlam : 0<lam) :
    connectedComponentIn (spectralSet lam)ᶜ 0=omegaH lam :=
  component_eq_of_frontier_subset (omegaH_isOpen hlam) (omegaH_isPreconnected hlam)
    (omegaH_subset_spectral_complement hlam) (frontier_omegaH_subset_spectralSet hlam)
    (zero_mem_omegaH hlam)

/-- Every positive supercritical point identifies the same full physical LT component. -/
theorem connectedComponentIn_spectral_complement_supercritical {lam : ℝ} (hlam : 0<lam)
    {x : ℝ} (hx : criticalPoint lam<x) :
    connectedComponentIn (spectralSet lam)ᶜ (x:ℂ)=omegaL lam :=
  component_eq_of_frontier_subset (omegaL_isOpen hlam) (omegaL_isPreconnected hlam)
    (omegaL_subset_spectral_complement hlam) (frontier_omegaL_subset_spectralSet hlam)
    ((real_mem_omegaL_iff hlam x).mpr hx)

end
end IsingBulk.Anisotropic
