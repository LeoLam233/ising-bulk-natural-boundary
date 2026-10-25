import IsingBulk.Joint.Negative.FamilyDominanceMiddle
import IsingBulk.Joint.Negative.FamilyDominancePrefactor
import IsingBulk.Anisotropic.NegativeDominance.GeometricDominance

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_middle_sum
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (q : ℕ) (hq : 0 < q) :
    ∃ Nlow N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧ n ≤ j ∧
      physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j ≠ 0 ∧
      ∀ Sf Sb : Finset ℕ, 0 ∉ Sf → 0 ∉ Sb →
      (∀ k ∈ Sf, 2*alpha (n+2*q+2*q*k) ≤ j) →
      (∀ k ∈ Sb, 2*q*k ≤ n+2*q ∧ Nlow ≤ n+2*q-2*q*k) →
      (∑ k ∈ Sf, ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q+2*q*k) j‖)+
      (∑ k ∈ Sb, ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q-2*q*k) j‖) ≤
        2*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖*
          (Real.exp (-((q : ℝ)^2/2*Real.log j))/
            (1-Real.exp (-((q : ℝ)^2/2*Real.log j)))) := by
  obtain ⟨Nlow, Ns, hs⟩ := compact_family_physical_model_middle_dominance B rootB phi hK hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨Np, hp⟩ := eventually_atTop.mp (compact_family_physical_prefactor_eventually_nonzero B rootB phi hK hB hB0 hroot hroot0 hsq hphi)
  refine ⟨Nlow, max Ns (max Np 2), ?_⟩
  intro eta heta n hn ho
  have hnNs : Ns≤n := (le_max_left _ _).trans hn
  have hnNp : Np≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : 2≤n := by omega
  obtain ⟨j, hjL, hjH, hnj, hAj, hf, hb⟩ := hs eta heta n hnNs ho
  have htj : alpha (n+2*q) ≤ j :=
    (alpha_mono (by omega : n+2*q≤n+4*q)).trans (by omega)
  have hw : physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j ≠ 0 :=
    model_ne_zero_of_prefactor _ _ _ _ _ _ (by omega) htj (hp _ (by omega) eta heta)
  refine ⟨j, hjL, hjH, hnj, hw, ?_⟩
  intro Sf Sb hSf hSb hSfA hSbA
  let a : ℝ := (q : ℝ)^2/2*Real.log j
  have ha : 0<a := by
    have hqR : 0<(q : ℝ) := by exact_mod_cast hq
    have hjR : 1<(j : ℝ) := by exact_mod_cast (show 1<j by omega)
    exact mul_pos (div_pos (sq_pos_of_pos hqR) (by norm_num)) (Real.log_pos hjR)
  have hsf := finite_norm_sum_of_log_gaps
    (fun k => physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q+2*q*k) j) _ hw a ha Sf hSf
    (fun k hk => hf k (hSfA k hk))
  have hsb := finite_norm_sum_of_log_gaps
    (fun k => physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q-2*q*k) j) _ hw a ha Sb hSb
    (fun k hk => hb k (hSbA k hk).1 (hSbA k hk).2)
  dsimp [a] at hsf hsb
  linarith only [hsf, hsb]


end
end IsingBulk.Joint.Negative
