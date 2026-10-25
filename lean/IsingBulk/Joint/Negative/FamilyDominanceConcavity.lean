import IsingBulk.Joint.Negative.FamilyDominanceData

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_second_difference_upper
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∀ j : ℕ,
      2 * alpha (n + 4 * p) ≤ j →
      Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n + 4 * p) j‖ -
        2 * Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n + 2 * p) j‖ +
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖ ≤
        -((2 * p : ℕ) : ℝ)^2 * Real.log j +
          ((2 * p : ℕ) : ℝ)^2 * modelQuadraticConstant (B (0,eta)) (Real.sin phi) +
          2 * ((2 * p : ℕ) : ℝ)^3 + 4 * C + 4 * ((2 * p : ℕ) : ℝ)^2 := by
  obtain ⟨C,Q,hC,_hQ,hdata⟩ := compact_family_model_data B rootB phi hK hB hB0 hroot hroot0 hsq
  obtain ⟨N,hN⟩ := eventually_atTop.mp hdata
  refine ⟨C, hC, max N 4, ?_⟩
  intro eta heta n hn ho j hj
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hA : 0 < alpha (n + 4 * p) := by
    have ht : 4 ≤ n + 4 * p := by omega
    have ht2 : 16 ≤ (n + 4 * p) * (n + 4 * p) := by nlinarith
    unfold alpha
    omega
  have hj' : alpha (n + 4 * p) < j := by omega
  have hbound := model_log_second_difference_upper
    (fun k => B (tau k,eta)) (fun k => rootB (tau k,eta))
    (fun k => hessianFactor (B (tau k,eta)) (Real.cos phi) (Real.sin phi) k)
    (B (0,eta)) (Real.sin phi) C n p j hn4 ho hj' hphi
    (fun k hk _ => by
      have ht := hN k (le_trans (le_max_left _ _) (hn.trans hk)) eta heta
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
    (fun k hk hok => (hN k (le_trans (le_max_left _ _) (hn.trans hk)) eta heta).2.2.2.2.1 hok)
  have hg := gamma_alpha_error_le_step_square n p j (by omega) ho hj
  change _ ≤ _ at hbound
  unfold physicalModel familyMember
  linarith

/-- Uniform strict concavity of the actual first-winding model on every
sufficiently large odd index with 2α_(n+4p)≤j. This includes the manuscript's
entire intermediate window for large j, not only a fixed relative window. -/

theorem compact_family_physical_model_strict_concavity
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0 < p) :
    ∃ N J : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∀ j ≥ J,
      2 * alpha (n + 4 * p) ≤ j →
      Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n + 4 * p) j‖ -
        2 * Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n + 2 * p) j‖ +
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖ ≤
        -(((2 * p : ℕ) : ℝ)^2 / 2) * Real.log j := by
  obtain ⟨C, hC, N, hN⟩ := compact_family_physical_model_second_difference_upper B rootB phi hK hB hB0 hroot hroot0 hsq hphi p
  let D : ℝ := ((2 * p : ℕ) : ℝ)
  obtain ⟨Q,_hQ,hQbound⟩ := compact_family_model_constants_bound B phi hK hB hB0
  let L := Q + 2 * D + 4 * C + 4
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 * L)))
  refine ⟨N, J, ?_⟩
  intro eta heta n hn ho j hj hja
  let q := modelQuadraticConstant (B (0,eta)) (Real.sin phi)
  have hb := hN eta heta n hn ho j hja
  have hlog := hJ j hj
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (by omega : 1 ≤ 2 * p)
  have hD2 : 1 ≤ D^2 := by nlinarith
  have hq := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr ((le_abs_self q).trans (hQbound eta heta).1))
  have hce := mul_nonneg (show 0 ≤ 4 * C by positivity) (sub_nonneg.mpr hD2)
  have hle := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hlog)
  change _ ≤ - (D^2 / 2) * Real.log j
  change _ ≤ -D^2 * Real.log j + D^2 * q + 2 * D^3 + 4 * C + 4 * D^2 at hb
  dsimp [L] at hle
  nlinarith


end
end IsingBulk.Joint.Negative
