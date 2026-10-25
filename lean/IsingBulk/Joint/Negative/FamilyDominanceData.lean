import IsingBulk.Joint.Negative.FamilyDominanceScalar

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Fiberwise root identities extend to one common disk by analytic uniqueness;
no uniform radius is requested as a premise. -/
theorem compact_family_square_identity (B rootB : ℂ × E → ℂ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta))
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta))
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) :
    ∃ r : ℝ, 0<r ∧ ∀ eta ∈ K, ∀ t : ℂ, ‖t‖<r → rootB (t,eta)^2=B (t,eta) := by
  obtain ⟨a,A,ha,_hA,hBa⟩ := compact_analytic_uniform_bound B hK hB
  obtain ⟨b,R,hb,_hR,hRa⟩ := compact_analytic_uniform_bound rootB hK hroot
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro eta heta
  have hBdisk : AnalyticOnNhd ℂ (fun t : ℂ => B (t,eta)) (ball 0 (min a b)) := by
    intro t ht
    exact (hBa eta heta t ((show ‖t‖<min a b by simpa using ht).trans_le (min_le_left _ _))).1.comp
      (f:=fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)
  have hRdisk : AnalyticOnNhd ℂ (fun t : ℂ => rootB (t,eta)^2) (ball 0 (min a b)) := by
    intro t ht
    exact ((hRa eta heta t ((show ‖t‖<min a b by simpa using ht).trans_le (min_le_right _ _))).1.comp
      (f:=fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)).pow 2
  have he := hRdisk.eqOn_of_preconnected_of_eventuallyEq hBdisk (convex_ball (0:ℂ) (min a b)).isPreconnected
    (mem_ball_self (lt_min ha hb)) (hsq eta heta)
  exact fun t ht => he (by simpa using ht)

/-- Common actual scalar model data. This contains only elementary B/root/Hessian
nonvanishing and a proved bounded analytic correction, not model dominance. -/
theorem compact_family_model_data (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) :
    ∃ C Q : ℝ, 0<C ∧ 0<Q ∧ ∀ᶠ n : ℕ in atTop, ∀ eta ∈ K,
      B (tau n,eta)≠0 ∧ rootB (tau n,eta)≠0 ∧
      hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n≠0 ∧
      rootB (tau n,eta)^2=B (tau n,eta) ∧
      (Odd n → |modelAnalyticError (B (0,eta)) (B (tau n,eta))
        (hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n) n|≤C) ∧
      |modelQuadraticConstant (B (0,eta)) (Real.sin phi)|≤Q ∧
      |modelAdditiveConstant (B (0,eta))|≤Q := by
  obtain ⟨C,hC,he⟩ := compact_family_modelAnalyticError_bound B phi hK hB hB0
  obtain ⟨Q,hQ,hconstant⟩ := compact_family_model_constants_bound B phi hK hB hB0
  obtain ⟨a,ha,hBn⟩ := compact_family_parameter_nonzero B hK hB hB0
  obtain ⟨b,hb,hRn⟩ := compact_family_parameter_nonzero rootB hK hroot hroot0
  obtain ⟨c,hc,hsquare⟩ := compact_family_square_identity B rootB hK hB hroot hsq
  obtain ⟨L,_hL,hH⟩ := compact_family_hessian_sequence B phi hK hB
  have hnear := tau_complex_tendsto_zero.eventually (ball_mem_nhds (0:ℂ) (lt_min ha (lt_min hb hc)))
  refine ⟨C,Q,hC,hQ,?_⟩
  filter_upwards [he,hH,hnear] with n hnerr hnH hnnear
  intro eta heta
  have hnorm : ‖(tau n:ℂ)‖<min a (min b c) := by simpa using hnnear
  refine ⟨(hBn eta heta _ (hnorm.trans_le (min_le_left _ _))).2,
    (hRn eta heta _ (hnorm.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).2,?_,
    hsquare eta heta _ (hnorm.trans_le ((min_le_right _ _).trans (min_le_right _ _))),
    hnerr eta heta,(hconstant eta heta).1,(hconstant eta heta).2⟩
  intro hz
  have hh := (hnH eta heta).2
  rw [hz,zero_sub,norm_neg,norm_one] at hh
  norm_num at hh

end
end IsingBulk.Joint.Negative
