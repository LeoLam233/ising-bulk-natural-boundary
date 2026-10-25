import IsingBulk.Joint.Negative.FamilyDominanceResonantSum
import IsingBulk.Anisotropic.NegativeDominance.ResonantMiddleSmall

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_resonant_middle_small
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p) {ε : ℝ} (hε : 0<ε) :
    ∃Nlow N : ℕ,∀ eta ∈ K, ∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j : ℝ) ∧
      (j : ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j≠0 ∧
      ∀I : Finset ℕ,ell+1∉I →
      (∀i∈I,2*alpha (resonantParticle p i)≤j) →
      (∀i∈I,Nlow≤resonantParticle p i) →
      (∑i∈I,‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j‖)≤
        ε*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j‖ := by
  obtain ⟨Nlow,N,hsel⟩ := compact_family_physical_resonant_middle_sum B rootB phi hK hB hB0 hroot hroot0 hsq hphi p hp hpOdd
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((middle_geometric_ratio_tendsto_zero hp).eventually_lt_const hε)
  refine ⟨Nlow,max N J,fun eta heta ell hell => ?_⟩
  obtain ⟨j,hjL,hjH,hnj,hm,hs⟩ := hsel eta heta ell (le_trans (le_max_left _ _) hell)
  refine ⟨j,hjL,hjH,hnj,hm,fun I hI hIA hIlow => ?_⟩
  have hh := hJ j ((le_max_right _ _).trans (hell.trans hnj))
  have hsum := hs I hI hIA hIlow
  have hmul := mul_le_mul_of_nonneg_right hh.le (norm_nonneg (physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j))
  nlinarith only [hsum,hmul]


end
end IsingBulk.Joint.Negative
