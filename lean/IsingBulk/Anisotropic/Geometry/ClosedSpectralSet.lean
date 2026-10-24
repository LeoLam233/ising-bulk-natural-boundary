import IsingBulk.Anisotropic.Geometry.Definitions
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section

/-- Compactness of the real square retains *all* degeneracies in the spectral set. -/
theorem spectralSet_isClosed (lam : ℝ) : IsClosed (spectralSet lam) := by
  let K := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let E : Set (ℂ × K) := {w | spectralA lam w.1 =
    spectralS w.1 * (w.2.1.1 : ℂ) + spectralT lam w.1 * (w.2.1.2 : ℂ)}
  have hE : IsClosed E := by
    apply isClosed_eq <;> dsimp only [spectralA, spectralS, spectralT] <;> fun_prop
  have heq : spectralSet lam = Prod.fst '' E := by
    ext z
    constructor
    · rintro ⟨u, hu, v, hv, h⟩
      exact ⟨(z, ⟨(u,v), hu,hv⟩), h, rfl⟩
    · rintro ⟨⟨w, ⟨⟨u,v⟩, hu,hv⟩⟩, h, rfl⟩
      exact ⟨u,hu,v,hv,h⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace E hE

end
end IsingBulk.Anisotropic
