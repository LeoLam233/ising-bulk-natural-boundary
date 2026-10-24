import IsingBulk.Anisotropic.NegativeDominance.CompleteCoefficientSelection
import IsingBulk.Anisotropic.NegativeDominance.SelectedGrowthRadius

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- Zero radius is derived from exact range decomposition and the Gamma model;
no complete-coefficient dominance or nonextension is assumed. -/
theorem complete_coefficient_radius_zero
    (coeff : ℕ→ℂ) (B rootB : ℂ→ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),rootB t^2=B t) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p)
    {a D C : ℝ} (ha : 0<a) (hD : 0<D) {eta : ℕ→ℝ}
    (heta : Tendsto eta atTop (𝓝 0))
    (hdecomp : ∀ᶠ j : ℕ in atTop,HasCoefficientRanges coeff B rootB phi p a D C eta j) :
    (FormalMultilinearSeries.ofScalars ℂ coeff).radius=0 := by
  obtain ⟨K,N,hsel⟩ := complete_coefficient_selected_growth coeff B rootB phi hB hB0 hroot hroot0 hsq hphi p hp hpOdd ha hD heta hdecomp
  apply radius_zero_of_resonant_selected_growth coeff hp K N
  intro ell hell
  obtain ⟨j,_hjL,_hjH,hnj,_hdom,hgrowth⟩ := hsel ell hell
  exact ⟨j,hnj,hgrowth⟩

end
end IsingBulk.Anisotropic.NegativeDominance
