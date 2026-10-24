import IsingBulk.Anisotropic.Geometry.DomainNonvanishing
import IsingBulk.Anisotropic.Geometry.Symmetry

namespace IsingBulk.Anisotropic
noncomputable section

/-- The complete unsquared spectral set cannot pass the positive critical line. -/
theorem spectral_re_le_criticalPoint {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈spectralSet lam) : z.re≤criticalPoint lam := by
  by_contra hn
  have hx : criticalPoint lam<z.re := lt_of_not_ge hn
  have hL : z∈omegaL lam := (sliceL_le_criticalPoint hlam z.im).trans_lt hx
  exact omegaL_subset_spectral_complement hlam hL hz

/-- The slab assertion in the physical spectral components theorem, including
all collinear, imaginary-axis and corner degeneracies. -/
theorem spectralSet_subset_critical_slab {lam : ℝ} (hlam : 0<lam) :
    spectralSet lam⊆{z : ℂ | |z.re|≤criticalPoint lam} := by
  intro z hz
  have hp := spectral_re_le_criticalPoint hlam hz
  have hn := spectral_re_le_criticalPoint hlam ((neg_mem_spectralSet_iff lam z).mpr hz)
  change -z.re≤criticalPoint lam at hn
  exact abs_le.mpr ⟨by linarith,hp⟩

end
end IsingBulk.Anisotropic
