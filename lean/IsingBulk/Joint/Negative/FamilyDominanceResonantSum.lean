import IsingBulk.Joint.Negative.FamilyDominanceMiddleSum
import IsingBulk.Anisotropic.NegativeDominance.ResonantProgression

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_resonant_middle_sum
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p) :
    ∃Nlow N : ℕ,∀ eta ∈ K, ∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j : ℝ) ∧
      (j : ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j≠0 ∧
      ∀I : Finset ℕ,ell+1∉I →
      (∀i∈I,2*alpha (resonantParticle p i)≤j) →
      (∀i∈I,Nlow≤resonantParticle p i) →
      (∑i∈I,‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j‖)≤
        2*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j‖*
          (Real.exp (-((p : ℝ)^2/2*Real.log j))/(1-Real.exp (-((p : ℝ)^2/2*Real.log j)))) := by
  classical
  obtain ⟨Nlow,N,hsel⟩ := compact_family_physical_model_middle_sum B rootB phi hK hB hB0 hroot hroot0 hsq hphi p hp
  refine ⟨Nlow,N,fun eta heta ell hell => ?_⟩
  have ho : Odd (resonantParticle p ell) := hpOdd.mul ⟨ell,rfl⟩
  obtain ⟨j,hjL,hjH,hnj,hm,hs⟩ := hsel eta heta _ hell ho
  have hcenter : resonantParticle p ell+2*p=resonantParticle p (ell+1) := by
    unfold resonantParticle
    ring
  rw [hcenter] at hm hs
  refine ⟨j,hjL,hjH,hnj,hm,fun I hI hIA hIlow => ?_⟩
  let Sf := (I.filter (fun i => ell+1< i)).image (fun i => i-(ell+1))
  let Sb := (I.filter (fun i => i<ell+1)).image (fun i => ell+1-i)
  have hSf : 0∉Sf := by
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hh := (Finset.mem_filter.mp hi).2
    omega
  have hSb : 0∉Sb := by
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hh := (Finset.mem_filter.mp hi).2
    omega
  have hSfA : ∀k∈Sf,2*alpha (resonantParticle p (ell+1)+2*p*k)≤j := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    rw [resonantParticle_forward p (ell+1) i (Nat.le_of_lt (Finset.mem_filter.mp hi).2)]
    exact hIA i (Finset.mem_filter.mp hi).1
  have hSbA : ∀k∈Sb,2*p*k≤resonantParticle p (ell+1) ∧
      Nlow≤resonantParticle p (ell+1)-2*p*k := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    have hic := Nat.le_of_lt (Finset.mem_filter.mp hi).2
    refine ⟨resonantParticle_backward_le p (ell+1) i hic,?_⟩
    rw [resonantParticle_backward p (ell+1) i hic]
    exact hIlow i (Finset.mem_filter.mp hi).1
  rw [finite_resonant_sum_partition p (ell+1) I hI (fun N => ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi N j‖)]
  exact hs Sf Sb hSf hSb hSfA hSbA


end
end IsingBulk.Joint.Negative
