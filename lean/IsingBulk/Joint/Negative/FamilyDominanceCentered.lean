import IsingBulk.Joint.Negative.FamilyDominanceCrossing
import IsingBulk.Anisotropic.NegativeDominance.DiscreteConcavity

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_centered_selection
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (q : ℕ) (hq : 0 < q) :
    ∃ N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧
      n ≤ j ∧ 2*alpha (n+4*q) ≤ j ∧
      |Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+4*q) j‖-
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖| ≤ 16*(q : ℝ)/(n : ℝ) ∧
      Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖ ≤
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖-(q : ℝ)^2/2*Real.log j ∧
      Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+4*q) j‖ ≤
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖-(q : ℝ)^2/2*Real.log j := by
  obtain ⟨Ns, hs⟩ := compact_family_physical_model_integer_selection B rootB phi hK hB hB0 hroot hroot0 hsq hphi (2*q) (by omega)
  obtain ⟨Nc, J, hc⟩ := compact_family_physical_model_strict_concavity B rootB phi hK hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_crossing_scale 64 (max Ns (max Nc (max J (max 16 (4*q))))))
  refine ⟨N, ?_⟩
  intro eta heta n hn ho
  obtain ⟨hnb, hnlog, hnupper⟩ := hN n hn
  have hnNs : Ns ≤ n := (le_max_left _ _).trans hnb
  have hnNc : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hnJ : J ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hnb))
  have hn16 : 16 ≤ n := by omega
  have hnq : 4*q ≤ n := by omega
  obtain ⟨j, hjL, hjH, _, hb⟩ := hs eta heta n hnNs ho
  have he : n+2*(2*q) = n+4*q := by ring
  rw [he] at hb
  have hb' : |Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+4*q) j‖-
      Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖| ≤ 16*(q : ℝ)/(n : ℝ) := by
    convert hb using 1
    push_cast
    ring
  have hr := crossing_order_range n (2*q) (by omega) (by omega) ho hnlog hnupper
  rw [he] at hr
  have hnjR : (n : ℝ)-1 < j := lt_of_le_of_lt (by linarith only [hr.2.1]) hjL
  have hnj : n ≤ j := by
    have hnat : n < j+1 := by exact_mod_cast (show (n : ℝ) < (j : ℝ)+1 by linarith only [hnjR])
    omega
  have hAj : 2*alpha (n+4*q) ≤ j := by exact_mod_cast ((hr.1.trans hjL.le))
  have hconc := hc eta heta n hnNc ho j (hnJ.trans hnj) hAj
  rw [neg_mul] at hconc
  have hadj := adjacent_bounds_of_balance hconc hb'
  have hn0 : (0 : ℝ) < n := by positivity
  have hn16R : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hjlog : 1 ≤ Real.log (j : ℝ) := by
    have hl := Real.log_le_log hn0 (show (n : ℝ) ≤ j by exact_mod_cast hnj)
    linarith only [hl, hnlog]
  have hsmall : 8*(q : ℝ)/(n : ℝ) ≤ (q : ℝ)^2/2*Real.log j := by
    calc
      _ ≤ (q : ℝ)/2 := by
        apply (div_le_iff₀ hn0).2
        nlinarith only [mul_le_mul_of_nonneg_left hn16R (show (0 : ℝ) ≤ q by positivity)]
      _ ≤ (q : ℝ)^2/2*Real.log j := by
        have hqq : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith only [hq1]
        have hm := mul_le_mul_of_nonneg_left hjlog (show 0 ≤ (q : ℝ)^2/2 by positivity)
        nlinarith only [hqq, hm]
  refine ⟨j, hjL, hjH, hnj, hAj, hb', ?_, ?_⟩
  · push_cast at hadj
    simp only [mul_div_assoc] at hadj hsmall ⊢
    nlinarith only [hadj.2, hsmall]
  · push_cast at hadj
    simp only [mul_div_assoc] at hadj hsmall ⊢
    nlinarith only [hadj.1, hsmall]


end
end IsingBulk.Joint.Negative
