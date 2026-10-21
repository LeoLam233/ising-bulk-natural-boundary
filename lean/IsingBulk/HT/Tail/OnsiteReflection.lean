import IsingBulk.HT.Final.OnsiteSymmetry
import IsingBulk.HT.Contour.SignedReflectionJets
import IsingBulk.HT.Lie.OnsiteFullSeries
import IsingBulk.HT.Tail.NegativeOriginalFamilyData
import IsingBulk.HT.Tail.OddIndexing

/-! Exact onsite reflection at every derivative order and complete-series
boundary bounds on the original positive and negative prime families. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Final IsingBulk.HT.Contour
open Filter Asymptotics
open scoped Topology

theorem onsiteFormFactor_reflected_odd_iteratedDeriv_norm (N : ℕ) (hN : Odd N)
    (r : ℝ) (s : ℂ) (j : ℕ) :
    ‖iteratedDeriv j (onsiteFormFactor N r) (-star s)‖ =
      ‖iteratedDeriv j (onsiteFormFactor N r) s‖ := by
  have he : (fun z => star (onsiteFormFactor N r (-star z))) =
      (fun z => -onsiteFormFactor N r z) := by
    funext z
    rw [onsiteFormFactor_neg_odd hN,onsiteFormFactor_conjugate]
    simp only [star_neg,star_star]
  have hh := iteratedDeriv_star_neg_conj j (onsiteFormFactor N r) s
  rw [he,iteratedDeriv_fun_neg] at hh
  have hn := congrArg norm hh
  simpa only [norm_neg,norm_mul,norm_pow,norm_one,one_pow,norm_star,one_mul] using hn.symm

/-- Fixed-radius germs are selected on both sides before differentiation. -/
theorem upperOnsiteFormFactor_reflected_odd_iteratedDeriv_norm
    (N : ℕ) (hN : Odd N) (hNpos : 0 < N) (s : ℂ)
    (hs : 0 < (sourceS s).im) (j : ℕ) :
    ‖iteratedDeriv j (upperOnsiteFormFactor N) (-star s)‖ =
      ‖iteratedDeriv j (upperOnsiteFormFactor N) s‖ := by
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hs
  have hm' : (canonicalRadius s)⁻¹-canonicalRadius s < (sourceS (-star s)).im := by
    simpa only [sourceS_neg_conjugate_im] using hm
  rw [upperOnsiteFormFactor_iteratedDeriv_fixed_radius N hNpos j hr hr1 hm',
    upperOnsiteFormFactor_iteratedDeriv_fixed_radius N hNpos j hr hr1 hm]
  exact onsiteFormFactor_reflected_odd_iteratedDeriv_norm N hN (canonicalRadius s) s j

theorem upperOnsiteFormFactor_reflected_radial_odd_iteratedDeriv_norm
    (N : ℕ) (hN : Odd N) (hNpos : 0 < N) {theta eps : ℝ}
    (htheta : 0 < Real.sin theta) (heps : 0 < eps) (j : ℕ) :
    ‖iteratedDeriv j (upperOnsiteFormFactor N) (radialParameter (Real.pi-theta) eps)‖ =
      ‖iteratedDeriv j (upperOnsiteFormFactor N) (radialParameter theta eps)‖ := by
  rw [radialParameter_neg_conjugate]
  exact upperOnsiteFormFactor_reflected_odd_iteratedDeriv_norm N hN hNpos _
    (IsingBulk.Final.sourceRadialTrace_pos htheta heps) j

theorem reflected_onsite_actual_odd_full_series_subpower (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter (Real.pi-d.theta) eps)‖)) ∧
    ∀ δ : ℝ,0 < δ →
      (fun eps : ℝ => ∑' n : ℕ,
        ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter (Real.pi-d.theta) eps)‖)
        =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  obtain ⟨hsum,hsmall⟩ := IsingBulk.HT.Lie.onsite_actual_odd_full_series_subpower d hcsmall j
  have ht : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (d.theta_lt.trans (by linarith [Real.pi_pos]))
  have he : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      (fun n : ℕ => ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter (Real.pi-d.theta) eps)‖) =
      (fun n : ℕ => ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter d.theta eps)‖) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    funext n
    exact upperOnsiteFormFactor_reflected_radial_odd_iteratedDeriv_norm (2*n+1)
      ⟨n,by omega⟩ (by omega) ht heps j
  constructor
  · filter_upwards [he,hsum] with eps hh hs
    rwa [hh]
  · intro δ hδ
    apply (hsmall δ hδ).congr'
    · filter_upwards [he] with eps hh
      exact congrArg (fun f : ℕ → ℝ => ∑' n,f n) hh.symm
    · exact Eventually.of_forall (fun _ => rfl)

theorem selected_positive_onsite_odd_series_subpower {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (fun eps : ℝ => ∑' n : ℕ,
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter (selectedOrderedChart ha hb).theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  simpa only [selectedLocalBranchData_theta] using
    (IsingBulk.HT.Lie.onsite_actual_odd_full_series_subpower
      (selectedLocalBranchData ha hb 1 1 zero_lt_one zero_lt_one)
      (selectedLocalBranchData_c0_small ha hb 1 1 zero_lt_one zero_lt_one) j).2 δ hδ

theorem negative_original_family_onsite_odd_series_subpower {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) (j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (fun eps : ℝ => ∑' n : ℕ,
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1))
        (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  have hh := (reflected_onsite_actual_odd_full_series_subpower
    (negativeOriginalReflectedData ha hb) (negativeOriginalReflectedData_c0_small ha hb) j).2 δ hδ
  rwa [negativeOriginalReflectedData_theta] at hh

/-- The literal canonical complex onsite series, with derivatives outside the
whole sum, inherits any actual whole absolute-series subpower estimate. -/
theorem upperOnsiteOddSeries_derivative_subpower_of_absolute {theta : ℝ}
    (htheta : 0 < Real.sin theta) (j : ℕ) (δ : ℝ)
    (hsmall : (fun eps : ℝ => ∑' n : ℕ,
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ))) :
    (fun eps : ℝ => iteratedDeriv j upperOnsiteOddSeries (radialParameter theta eps))
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  have hb : (fun eps : ℝ => iteratedDeriv j upperOnsiteOddSeries (radialParameter theta eps))
      =O[𝓝[>] 0] (fun eps : ℝ => ∑' n : ℕ,
        ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter theta eps)‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have hs := IsingBulk.Final.sourceRadialTrace_pos htheta heps
    rw [upperOnsiteOddSeries_iteratedDeriv j hs]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _)),one_mul]
      using norm_tsum_le_tsum_norm (upperOnsiteOdd_derivative_summable j hs)
  exact hb.trans_isLittleO hsmall

theorem selected_positive_onsite_derivative_subpower {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (fun eps : ℝ => iteratedDeriv j upperOnsiteOddSeries
      (radialParameter (selectedOrderedChart ha hb).theta eps))
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) :=
  upperOnsiteOddSeries_derivative_subpower_of_absolute (selectedOrderedChart ha hb).sin_theta_pos
    j δ (selected_positive_onsite_odd_series_subpower ha hb j δ hδ)

theorem negative_original_family_onsite_derivative_subpower {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) (j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (fun eps : ℝ => iteratedDeriv j upperOnsiteOddSeries
      (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta eps))
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) :=
  upperOnsiteOddSeries_derivative_subpower_of_absolute
    (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).sin_theta_pos
    j δ (negative_original_family_onsite_odd_series_subpower ha hb j δ hδ)

end
end IsingBulk.HT.Tail
