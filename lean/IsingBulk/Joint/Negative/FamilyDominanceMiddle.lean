import IsingBulk.Joint.Negative.FamilyDominanceCentered
import IsingBulk.Anisotropic.NegativeDominance.LatticeDecay

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_middle_dominance
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (q : ℕ) (hq : 0 < q) :
    ∃ Nlow N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧ n ≤ j ∧ 2*alpha (n+4*q) ≤ j ∧
      (∀ k : ℕ, 2*alpha (n+2*q+2*q*k) ≤ j →
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q+2*q*k) j‖ ≤
          Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖-
            ((q : ℝ)^2/2*Real.log j)*(k : ℝ)) ∧
      (∀ k : ℕ, 2*q*k ≤ n+2*q → Nlow ≤ n+2*q-2*q*k →
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q-2*q*k) j‖ ≤
          Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖-
            ((q : ℝ)^2/2*Real.log j)*(k : ℝ)) := by
  obtain ⟨Ns, hs⟩ := compact_family_physical_model_centered_selection B rootB phi hK hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨Nc, J, hc⟩ := compact_family_physical_model_strict_concavity B rootB phi hK hB hB0 hroot hroot0 hsq hphi q hq
  refine ⟨Nc, max Ns (max Nc (max J 2)), ?_⟩
  intro eta heta n hn ho
  have hnNs : Ns ≤ n := (le_max_left _ _).trans hn
  have hnNc : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnJ : J ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn2 : 2 ≤ n := by omega
  obtain ⟨j, hjL, hjH, hnj, hAj, _, hminus, hplus⟩ := hs eta heta n hnNs ho
  have hjJ : J ≤ j := hnJ.trans hnj
  have hjlog : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤j by omega))
  let f : ℕ → ℝ := fun m => Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi m j‖
  let a : ℝ := (q : ℝ)^2/2*Real.log j
  have hnonpos (U : ℕ) (hU : 2*alpha U ≤ j) (m : ℕ)
      (hm : Nc ≤ m) (hom : Odd m) (hmU : m+4*q ≤ U) :
      f (m+4*q)-2*f (m+2*q)+f m ≤ 0 := by
    have hgam : 2*alpha (m+4*q) ≤ j := (Nat.mul_le_mul_left 2 (alpha_mono hmU)).trans hU
    have hh := hc eta heta m hm hom j hjJ hgam
    have hnon : -(((2*q : ℕ) : ℝ)^2/2)*Real.log (j : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hjlog
    exact hh.trans hnon
  have hot : Odd (n+2*q) := by obtain ⟨v, rfl⟩ := ho; exact ⟨v+q, by ring⟩
  have hfirstplus : f (n+2*q+2*q)-f (n+2*q) ≤ -a := by
    have he : n+2*q+2*q=n+4*q := by ring
    dsimp [f, a]
    rw [he]
    linarith only [hplus]
  have hfirstminus : f (n+2*q-2*q)-f (n+2*q) ≤ -a := by
    dsimp [f, a]
    rw [Nat.add_sub_cancel]
    linarith only [hminus]
  refine ⟨j, hjL, hjH, hnj, hAj, ?_, ?_⟩
  · intro k hk
    exact lattice_linear_forward f a q Nc (n+2*q+2*q*k) (n+2*q) k hot
      (by omega) le_rfl (hnonpos _ hk) hfirstplus
  · intro k hkt hkN
    have htA : 2*alpha (n+2*q) ≤ j :=
      (Nat.mul_le_mul_left 2 (alpha_mono (by omega : n+2*q≤n+4*q))).trans hAj
    exact lattice_linear_backward f a q Nc (n+2*q) (n+2*q) k hot hkN hkt le_rfl
      (hnonpos _ htA) hfirstminus


end
end IsingBulk.Joint.Negative
