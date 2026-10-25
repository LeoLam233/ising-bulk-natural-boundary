import IsingBulk.Joint.Negative.FamilyDominanceData

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual prefactor is nonzero on one common tail of particle indices. -/
theorem compact_family_physical_prefactor_eventually_nonzero
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0) :
    ∀ᶠ n : ℕ in atTop, ∀ eta ∈ K, modelPrefactor (B (tau n,eta)) (rootB (tau n,eta))
      (hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n) (Real.sin phi) n≠0 := by
  obtain ⟨C,Q,_hC,_hQ,hdata⟩ := compact_family_model_data B rootB phi hK hB hB0 hroot hroot0 hsq
  filter_upwards [hdata,eventually_ge_atTop (1:ℕ)] with n hn hnpos
  intro eta heta
  have h := hn eta heta
  exact modelPrefactor_ne_zero _ _ _ _ n h.1 h.2.1 h.2.2.1 hphi (by omega)

end
end IsingBulk.Joint.Negative
