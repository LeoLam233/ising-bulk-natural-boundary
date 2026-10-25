import IsingBulk.Joint.Negative.FamilyDominanceConcavity

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_model_integer_selection
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ eta ∈ K, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧
      alpha (n+2*p) < j ∧
      |Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*p) j‖-
        Real.log ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi n j‖| ≤ 8*(p : ℝ)/(n : ℝ) := by
  obtain ⟨C,Q,hC,_hQ,hdata⟩ := compact_family_model_data B rootB phi hK hB hB0 hroot hroot0 hsq
  obtain ⟨N,hN⟩ := eventually_atTop.mp hdata
  have hscale := eventually_crossing_scale
    (max 64 (2*(2*Q+14+2*C)+2))
    (max N (max 2 (2*p)))
  have hpi : ∀ᶠ n : ℕ in atTop, Real.pi^2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.pi^2))
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hscale.and hpi)
  refine ⟨N', ?_⟩
  intro eta heta n hn ho
  have hsc := (hN' n hn).1
  have hpi' := (hN' n hn).2
  have hnN : N ≤ n := (le_max_left _ _).trans hsc.1
  have hn2 : 2 ≤ n := (le_max_left 2 (2*p)).trans ((le_max_right N _).trans hsc.1)
  have hnp : 2*p ≤ n := (le_max_right 2 (2*p)).trans ((le_max_right N _).trans hsc.1)
  have hQn := (hN n hnN eta heta).2.2.2.2.2.1
  have hlog : max 64 (2*(2*|modelQuadraticConstant (B (0,eta)) (Real.sin phi)|+14+2*C)+2)≤Real.log n :=
    (max_le_max le_rfl (by linarith)).trans hsc.2.1
  have hsel := exists_integer_model_balance
    (fun k => B (tau k,eta)) (fun k => rootB (tau k,eta))
    (fun k => hessianFactor (B (tau k,eta)) (Real.cos phi) (Real.sin phi) k)
    (B (0,eta)) (Real.sin phi) C n p hn2 hp hnp hpi' ho hC.le hphi hlog hsc.2.2
    (fun k hk _ => by
      have ht := hN k (hnN.trans hk) eta heta
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
    (fun k hk hok => (hN k (hnN.trans hk) eta heta).2.2.2.2.1 hok)
  simpa only [physicalModel,familyMember] using hsel


end
end IsingBulk.Joint.Negative
