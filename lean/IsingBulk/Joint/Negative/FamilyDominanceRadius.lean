import IsingBulk.Joint.Negative.FamilyDominanceSelection

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_complete_coefficient_radius_zero
    (coeff : E→ℕ→ℂ) (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p)
    {a D C : ℝ} (ha : 0<a) (hD : 0<D) {err : ℕ→ℝ}
    (herrto0 : Tendsto err atTop (𝓝 0))
    (hdecomp : ∀ᶠ j : ℕ in atTop,∀ eta ∈ K, HasCoefficientRanges (coeff eta) (familyMember B eta) (familyMember rootB eta) phi p a D C err j) :
    ∀ eta ∈ K, (FormalMultilinearSeries.ofScalars ℂ (coeff eta)).radius=0 := by
  obtain ⟨G,N,hsel⟩ := compact_family_complete_coefficient_selected_growth coeff B rootB phi hK hB hB0 hroot hroot0 hsq hphi p hp hpOdd ha hD herrto0 hdecomp
  intro eta heta
  apply radius_zero_of_resonant_selected_growth (coeff eta) hp G N
  intro ell hell
  obtain ⟨j,_hjL,_hjH,hnj,_hdom,hgrowth⟩ := hsel eta heta ell hell
  exact ⟨j,hnj,hgrowth⟩


end
end IsingBulk.Joint.Negative
