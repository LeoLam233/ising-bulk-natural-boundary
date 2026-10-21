import IsingBulk.HT.Lie.OnsiteSeriesBudget
import IsingBulk.HT.Contour.OnsiteGaussianSectorIntegral
import IsingBulk.HT.Final.UpperOnsiteSeries
import IsingBulk.Tail.RadialSourceDomain

/-! The actual full odd onsite boundary series. All particle orders,
including N=1, are controlled before the radial limit. Finite-order selector
and deformation choices disappear through the literal canonical F+K+S identity. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Final
  Set Filter MeasureTheory Asymptotics
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- HT onsitesum at the literal canonical onsite source: every fixed
parameter derivative of the complete odd absolute series is subpower. -/
theorem onsite_actual_odd_full_series_subpower (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (j : ℕ) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter d.theta eps)‖)) ∧
    ∀ δ : ℝ,0<δ →
      (fun eps : ℝ => ∑' n : ℕ,
        ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter d.theta eps)‖)
        =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  obtain ⟨ηF,τF,hηF,hτF,hFsetup⟩ := onsite_odd_selected_actual_full_series_reqF d hcsmall
  obtain ⟨ηK,hηK,hKsetup⟩ := onsite_original_sector_derivative_gaussian d hcsmall
  obtain ⟨ηS,hηS,hSsetup⟩ := onsite_current_sector_derivative_gaussian d hcsmall
  let ηcap := min ηF (min ηK (min ηS (Real.sin d.thetaB/4)))
  have hηcap : 0<ηcap := by dsimp [ηcap]; positivity [d.a_pos]
  let η := ηcap/2
  have hη : 0<η := half_pos hηcap
  have hηlt : η<ηcap := half_lt_self hηcap
  have hηF' : η<ηF := hηlt.trans_le (min_le_left _ _)
  have hηK' : η<ηK := hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηS' : η<ηS := hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨αK,κK,hαK,hκK,hKsetup⟩ := hKsetup η hη hηK'
  obtain ⟨αS,hαS,hSsetup⟩ := hSsetup η hη hηS'
  let αcap := min αK (min αS (Real.sin d.thetaB/4))
  have hαcap : 0<αcap := by dsimp [αcap]; positivity [d.a_pos]
  let α := αcap/2
  have hα : 0<α := half_pos hαcap
  have hαlt : α<αcap := half_lt_self hαcap
  have hαK' : α<αK := hαlt.trans_le (min_le_left _ _)
  have hαS' : α<αS := hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαsmall : α<Real.sin d.thetaB/4 := hαlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨iK,hiK,_hiKcap,hKsetup⟩ := hKsetup α hα hαK' j 1 zero_lt_one
  obtain ⟨iS,hiS,_hiScap,hSsetup⟩ := hSsetup α hα hαS' j 1 zero_lt_one
  let inner := min iK iS/2
  have hi : 0< inner := half_pos (lt_min hiK hiS)
  have hilt : inner<min iK iS := half_lt_self (lt_min hiK hiS)
  obtain ⟨eK,CK,heK,hCK,hKbound⟩ := hKsetup inner hi (hilt.le.trans (min_le_left _ _))
  obtain ⟨τS,hτS,hSsetup⟩ := hSsetup inner hi (hilt.le.trans (min_le_right _ _))
  let τ := min τF τS/2
  have hτ : 0<τ := half_pos (lt_min hτF hτS)
  have hτlt : τ<min τF τS := half_lt_self (lt_min hτF hτS)
  have hτF' : τ<τF := hτlt.trans_le (min_le_left _ _)
  have hτS' : τ<τS := hτlt.trans_le (min_le_right _ _)
  obtain ⟨κS,eS,CS,hκS,heS,hCS,hSbound⟩ := hSsetup τ hτ hτS'
  obtain ⟨eF,CF,heF,hCF,hFbound⟩ := hFsetup η α τ hη hηF' hα hαsmall hτ hτF' j
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  let F := fun eps : ℝ => fun n : ℕ => ‖iteratedDeriv j
    (onsiteSelectedIntegral (2*n+1) f (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖
  let K := fun eps : ℝ => fun n : ℕ => ‖iteratedDeriv j
    (onsiteOriginalLowerIntegral (2*n+1) f (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖
  let S := fun eps : ℝ => fun n : ℕ => ‖iteratedDeriv j
    (onsiteCurrentIntegral (2*n+1) f (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖
  have hKmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0,∀ n,K eps n≤
      (3*CK)^(2*n+1)*((2*n+1:ℕ):ℝ)^(5*j)*Real.exp (-κK*((2*n+1:ℕ):ℝ)^2) := by
    filter_upwards [self_mem_nhdsWithin,radial_source_eventually_damping d hcsmall,
      (show ∀ᶠ eps : ℝ in 𝓝[>] 0,eps<eK from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds heK))] with eps heps hdom hsmall
    intro n
    have hh := onsite_original_derivative_sector_bound (2*n+1) (by omega) f hf hdom.1 hdom.2.1 hτ.le
      d.thetaB inner hi hdom.2.2 j
      (fun sigma => hKbound (2*n) j eps τ sigma le_rfl heps hsmall hτ.le)
    apply hh.trans_eq
    rw [mul_pow]
    ring
  have hSmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0,∀ n,S eps n≤
      (3*CS)^(2*n+1)*((2*n+1:ℕ):ℝ)^(5*j+1)*Real.exp (-κS*((2*n+1:ℕ):ℝ)^2) := by
    filter_upwards [self_mem_nhdsWithin,radial_source_eventually_damping d hcsmall,
      (show ∀ᶠ eps : ℝ in 𝓝[>] 0,eps<eS from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds heS))] with eps heps hdom hsmall
    intro n
    have hh := onsite_current_derivative_sector_bound (2*n+1) (by omega) f hf hdom.1 hdom.2.1 hτ.le
      d.thetaB inner hi hdom.2.2 j
      (fun lam hlam q sigma => hSbound (2*n) j eps lam q sigma le_rfl heps hsmall hlam.1 hlam.2)
    apply hh.trans_eq
    rw [mul_pow,pow_succ (((2*n+1:ℕ):ℝ)) (5*j)]
    ring
  obtain ⟨hKsum,hKsmall⟩ := onsite_odd_gaussian_series_subpower K (5*j) (by positivity) hκK
    (fun _ _ => norm_nonneg _) hKmajor
  obtain ⟨hSsum,hSsmall⟩ := onsite_odd_gaussian_series_subpower S (5*j+1) (by positivity) hκS
    (fun _ _ => norm_nonneg _) hSmajor
  have hFdata : ∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (F eps) ∧
      (∑' n,F eps n)≤Real.exp (CF*Real.log (2-Real.log eps)^2) := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ eps : ℝ in 𝓝[>] 0,eps<eF from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds heF))] with eps heps hsmall
    exact hFbound eps heps hsmall
  have hFbig : (fun eps : ℝ => ∑' n,F eps n) =O[𝓝[>] 0]
      (fun eps : ℝ => Real.exp (CF*Real.log (2-Real.log eps)^2)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hFdata] with eps heps
    have hnon : 0 ≤ ∑' n,F eps n := tsum_nonneg (fun _ => norm_nonneg _)
    simpa only [Real.norm_eq_abs,abs_of_nonneg hnon,
      abs_of_pos (Real.exp_pos _),one_mul] using heps.2
  have hsource : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      Summable (fun n : ℕ => ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter d.theta eps)‖) ∧
      (∑' n : ℕ,‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter d.theta eps)‖)≤
        (∑' n,F eps n)+(∑' n,K eps n)+(∑' n,S eps n) := by
    filter_upwards [hFdata,hKsum,hSsum,radial_source_eventually_damping d hcsmall]
      with eps hF hK hS hdom
    have hpoint (n : ℕ) : ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter d.theta eps)‖≤F eps n+K eps n+S eps n := by
      rw [upperOnsiteFormFactor_selector_iteratedDeriv (2*n+1) (by omega) f hf
        hdom.1 hdom.2.1 hτ.le hdom.2.2 j]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint ((hF.1.add hK).add hS)
    refine ⟨hs,?_⟩
    have hh := Summable.tsum_le_tsum hpoint hs ((hF.1.add hK).add hS)
    simpa only [(hF.1.add hK).tsum_add hS,hF.1.tsum_add hK] using hh
  refine ⟨hsource.mono (fun _ h => h.1),?_⟩
  intro δ hδ
  have htotal := ((hFbig.trans_isLittleO (radial_log_square_growth_littleO_rpow CF hδ)).add
    (hKsmall δ hδ)).add (hSsmall δ hδ)
  have hdom : (fun eps : ℝ => ∑' n : ℕ,‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
      (radialParameter d.theta eps)‖) =O[𝓝[>] 0]
        (fun eps => (∑' n,F eps n)+(∑' n,K eps n)+(∑' n,S eps n)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hsource] with eps heps
    have hnon : 0≤(∑' n,F eps n)+(∑' n,K eps n)+(∑' n,S eps n) :=
      add_nonneg (add_nonneg (tsum_nonneg (fun _ => norm_nonneg _))
        (tsum_nonneg (fun _ => norm_nonneg _))) (tsum_nonneg (fun _ => norm_nonneg _))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _)),
      abs_of_nonneg hnon,one_mul] using heps.2
  exact hdom.trans_isLittleO htotal

end
end IsingBulk.HT.Lie
