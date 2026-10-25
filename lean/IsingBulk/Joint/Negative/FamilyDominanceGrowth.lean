import IsingBulk.Joint.Negative.FamilyDominanceData
import IsingBulk.Anisotropic.NegativeDominance.ModelGrowth

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_growth_bound
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ L : ℝ, ∃ N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∀ j : ℕ,
      alpha n<j → j≤n^3 → 1≤Real.log n →
      (n : ℝ)^2*Real.log n≤A*(j : ℝ) →
      (j : ℝ)*(2*Real.log n-L) ≤ Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖ := by
  obtain ⟨C,Q,hC,_hQ,hdata⟩ := compact_family_model_data B rootB phi hK hB hB0 hroot hroot0 hsq
  obtain ⟨N,hN⟩ := eventually_atTop.mp hdata
  let L := A*(8+Q+Real.log Real.pi)+|entropyPart 2|+Q+C+Real.log (Real.pi^2/2)
  refine ⟨L,max N 2,?_⟩
  intro eta heta n hn ho j hj hjH hlog hscale
  have hgood := hN n ((le_max_left _ _).trans hn) eta heta
  have hg := log_norm_model_growth _ _ _ _ _ A C n j (by omega) ho hj hjH hlog hA hC.le hscale
    hgood.1 hgood.2.1 hgood.2.2.1 hphi hgood.2.2.2.1 (hgood.2.2.2.2.1 ho)
  have hq := mul_le_mul_of_nonneg_left hgood.2.2.2.2.2.1 hA
  have hloss : growthLoss (B (0,eta)) (Real.sin phi) A C≤L := by
    dsimp [growthLoss,L]
    linarith [hgood.2.2.2.2.2.2]
  change _≤Real.log ‖model _ _ _ _ _ _‖
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hloss _) (Nat.cast_nonneg j)).trans hg


end
end IsingBulk.Joint.Negative
