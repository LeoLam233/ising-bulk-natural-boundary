import IsingBulk.Anisotropic.NegativeDominance.ResonantProgression

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Single-index selection on the actual resonant odd-multiple progression.
Every other resonant index in the complete middle Gamma range is included. -/
theorem physical_resonant_middle_sum
    (B rootB : ℂ→ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),rootB t^2=B t) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p) :
    ∃Nlow N : ℕ,∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j : ℝ) ∧
      (j : ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      physicalModel B rootB phi (resonantParticle p (ell+1)) j≠0 ∧
      ∀I : Finset ℕ,ell+1∉I →
      (∀i∈I,2*alpha (resonantParticle p i)≤j) →
      (∀i∈I,Nlow≤resonantParticle p i) →
      (∑i∈I,‖physicalModel B rootB phi (resonantParticle p i) j‖)≤
        2*‖physicalModel B rootB phi (resonantParticle p (ell+1)) j‖*
          (Real.exp (-((p : ℝ)^2/2*Real.log j))/(1-Real.exp (-((p : ℝ)^2/2*Real.log j)))) := by
  classical
  obtain ⟨Nlow,N,hsel⟩ := physical_model_middle_sum B rootB phi hB hB0 hroot hroot0 hsq hphi p hp
  refine ⟨Nlow,N,fun ell hell => ?_⟩
  have ho : Odd (resonantParticle p ell) := hpOdd.mul ⟨ell,rfl⟩
  obtain ⟨j,hjL,hjH,hnj,hm,hs⟩ := hsel _ hell ho
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
  rw [finite_resonant_sum_partition p (ell+1) I hI (fun N => ‖physicalModel B rootB phi N j‖)]
  exact hs Sf Sb hSf hSb hSfA hSbA

end
end IsingBulk.Anisotropic.NegativeDominance
