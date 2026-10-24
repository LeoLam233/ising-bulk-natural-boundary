import IsingBulk.Anisotropic.Final.Target
import IsingBulk.Anisotropic.Geometry.BoundaryProfiles
import IsingBulk.Anisotropic.Geometry.HighTopology

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem high_boundary_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) : z ≠ 0 := by
  intro he
  subst z
  rw [(omegaH_isOpen hlam).frontier_eq] at hz
  exact hz.2 (zero_mem_omegaH hlam)

theorem low_boundary_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) : z ≠ 0 := by
  intro he
  subst z
  have hgraph := (mem_frontier_omegaL_iff hlam (0:ℂ)).mp hz
  have hh : sliceL lam 0 = criticalPoint lam := by
    simp only [sliceL,Real.cos_zero,mul_zero,abs_one,sliceQInv_one hlam]
    simp [criticalPoint]
  have hp := criticalPoint_pos hlam
  simp only [Complex.zero_re,Complex.zero_im,hh] at hgraph
  linarith

theorem fullAnalyticConclusion_of_normalized {J lam : ℝ} (hJ : 0 < J)
    (hlam : 0 < lam)
    (hH : NaturalBoundaryOn (omegaH lam) (FormFactors.highNormalizedBulk lam))
    (hL : NaturalBoundaryOn (omegaL lam) (FormFactors.lowNormalizedBulk lam)) :
    FullAnalyticConclusion J lam := by
  refine ⟨hH,hL,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro z hz
    exact (inverseTemperature_analytic J z).mul (hH.1 z hz)
  · intro z hz
    exact physical_response_no_extension hJ (high_boundary_ne_zero hlam hz) (hH.2 z hz)
  · intro z hz
    exact (inverseTemperature_analytic J z).mul (hL.1 z hz)
  · intro z hz
    exact physical_response_no_extension hJ (low_boundary_ne_zero hlam hz) (hL.2 z hz)

end
end IsingBulk.Anisotropic
