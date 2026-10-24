import IsingBulk.Anisotropic.NegativeDominance.CompleteCoefficientRadius
import IsingBulk.Anisotropic.NegativeDominance.PaperModelData

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter RegularEdges
open scoped Topology

/-- Actual complete weighted HT coefficient series. All model branch inputs
are derived from the physical chart. The remaining internal input is the
literal range decomposition, to be discharged by physical period estimates. -/
theorem negative_paper_coefficient_radius_zero_of_ranges
    {lam : ℝ} {z : ℂ} (hd : spectralDet lam z<0)
    {zeta A : ℂ→ℂ} (hz : zeta 0=z) (hza : AnalyticAt ℂ zeta 0)
    (hAa : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),A t^2=spectralProduct lam (zeta t))
    (phi : ℝ) (hphi : Real.sin phi≠0) (p : ℕ) (hp : 0<p) (hpOdd : Odd p)
    {a D C : ℝ} (ha : 0<a) (hD : 0<D) {eta : ℕ→ℝ}
    (heta : Tendsto eta atTop (𝓝 0))
    (hdecomp : ∀ᶠ j : ℕ in atTop,HasCoefficientRanges (negativePaperCoefficient lam zeta A)
      (paperModelB lam zeta) (paperModelRoot zeta A) phi p a D C eta j) :
    (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient lam zeta A)).radius=0 := by
  obtain ⟨hB,hB0,hr,hr0,hs⟩ := paper_model_data hd hz hza hAa hA0 hsq
  exact complete_coefficient_radius_zero _ _ _ phi hB hB0 hr.continuousAt hr0 hs hphi p hp hpOdd ha hD heta hdecomp

end
end IsingBulk.Anisotropic.NegativeDominance
