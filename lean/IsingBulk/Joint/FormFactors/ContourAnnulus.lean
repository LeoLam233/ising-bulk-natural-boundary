import IsingBulk.Joint.FormFactors.ComplexContours
import IsingBulk.Anisotropic.FormFactors.ContourAnnulus

/-! The JOINT torus gap uses the unsquared spectral condition, including both axes.
The compact inner-annulus theorem is reused verbatim from the verified baseline. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Metric IsingBulk.First IsingBulk.Anisotropic.FormFactors

theorem torus_dispersion_ne_zero {K : Coupling} (hK : K ∉ spectralSet)
    {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : dispersion K x y ≠ 0 := by
  intro h
  apply hK
  refine ⟨x.re, Anisotropic.unit_re_mem_Icc x hx, y.re,
    Anisotropic.unit_re_mem_Icc y hy, ?_⟩
  unfold dispersion dispersionPolynomial at h
  rw [Anisotropic.unit_trace x hx, Anisotropic.unit_trace y hy] at h
  linear_combination h

theorem contourAnnulus_exists {K : Coupling} (hK : K ∉ spectralSet) :
    ∃ r, ContourAnnulus K r := by
  apply Anisotropic.FormFactors.exists_inner_annulus (fun v => dispersion K v.1 v.2)
  · intro v hv1 hv2
    unfold dispersion dispersionPolynomial
    exact (continuousAt_const.sub
      (continuousAt_const.mul (continuousAt_fst.add (continuousAt_fst.inv₀ hv1)))).sub
      (continuousAt_const.mul (continuousAt_snd.add (continuousAt_snd.inv₀ hv2)))
  · intro x y hx hy
    exact torus_dispersion_ne_zero hK hx hy

theorem contourRadius_valid {K : Coupling} (hK : K ∉ spectralSet) :
    ContourAnnulus K (contourRadius K) := contourRadius_spec (contourAnnulus_exists hK)
end
end IsingBulk.Joint.FormFactors
