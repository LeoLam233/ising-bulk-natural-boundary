import IsingBulk.Anisotropic.NegativeDominance.ModelGrowth

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The main-model logarithmic growth estimate with all analytic-error and
nonvanishing premises discharged from the actual scalar analytic branch. -/
theorem physical_model_growth_bound
    (B rootB : ℂ → ℂ) (phi A : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2 = B t) (hphi : Real.sin phi ≠ 0)
    (hA : 0≤A) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, Odd n → ∀ j : ℕ,
      alpha n<j → j≤n^3 → 1≤Real.log n →
      (n : ℝ)^2*Real.log n≤A*(j : ℝ) →
      (j : ℝ)*(2*Real.log n-K) ≤ Real.log ‖physicalModel B rootB phi n j‖ := by
  obtain ⟨C, hC, he⟩ := physical_modelAnalyticError_eventually_bounded B phi hB hB0
  have hb := tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0)
  have hr := tau_complex_tendsto_zero.eventually (hroot.eventually_ne hroot0)
  have hh := hessianFactor_eventually_nonzero B phi hB
  have hsqn := tau_complex_tendsto_zero.eventually hsq
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.and (hr.and (hh.and (hsqn.and he))))
  refine ⟨growthLoss (B 0) (Real.sin phi) A C, max N 2, ?_⟩
  intro n hn ho j hj hjH hlog hscale
  have hgood := hN n ((le_max_left _ _).trans hn)
  exact log_norm_model_growth _ _ _ _ _ A C n j (by omega) ho hj hjH hlog hA hC.le hscale
    hgood.1 hgood.2.1 hgood.2.2.1 hphi hgood.2.2.2.1 (hgood.2.2.2.2 ho)

/-- Selected main models grow faster than every geometric sequence in j:
the lower logarithmic rate is 2 log n minus one fixed constant. This remains
a statement about the exact model, not about complete susceptibility jets. -/
theorem physical_selected_model_growth
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2 = B t) (hphi : Real.sin phi ≠ 0)
    (q : ℕ) (hq : 0<q) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) ∧ (j : ℝ)≤upperCrossingOrder n ∧ n≤j ∧
      (j : ℝ)*(2*Real.log n-K)≤Real.log ‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨K, Ng, hg⟩ := physical_model_growth_bound B rootB phi 32 hB hB0 hroot hroot0 hsq hphi (by norm_num)
  obtain ⟨Ns, hs⟩ := physical_model_centered_selection B rootB phi hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_crossing_scale 64 (max Ng (max Ns 2)))
  refine ⟨K, N, ?_⟩
  intro n hn ho
  obtain ⟨hnb, hnlog, hnupper⟩ := hN n hn
  have hnNg : Ng≤n := (le_max_left _ _).trans hnb
  have hnNs : Ns≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hn2 : 2≤n := by omega
  obtain ⟨j, hjL, hjH, hnj, hAj, _, hminus, _⟩ := hs n hnNs ho
  have hmono : 2*alpha n≤j :=
    (Nat.mul_le_mul_left 2 (alpha_mono (by omega : n≤n+4*q))).trans hAj
  have hj : alpha n<j := by omega
  have hjH' : j≤n^3 := by
    have h := mul_le_mul_of_nonneg_left hnupper (sq_nonneg (n : ℝ))
    dsimp [upperCrossingOrder] at hjH
    have he : (j : ℝ)≤(n : ℝ)^3 := by nlinarith only [h,hjH]
    exact_mod_cast he
  have hscale : (n : ℝ)^2*Real.log n≤32*(j : ℝ) := by
    have hnR : (2 : ℝ)≤n := by exact_mod_cast hn2
    have hp : (4 : ℝ)≤(n : ℝ)^2 := by nlinarith only [hnR]
    have hlarge : 32≤(n : ℝ)^2*Real.log n := by nlinarith only [hp,hnlog]
    dsimp [lowerCrossingOrder] at hjL
    linarith only [hjL,hlarge]
  have hgrow := hg n hnNg ho j hj hjH' (by linarith only [hnlog]) hscale
  have hlogj : 0≤Real.log (j : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤j by omega))
  have hgap : 0≤(q : ℝ)^2/2*Real.log j := by positivity
  refine ⟨j, hjL, hjH, hnj, ?_⟩
  linarith only [hgrow,hminus,hgap]

end
end IsingBulk.Anisotropic.NegativeDominance
