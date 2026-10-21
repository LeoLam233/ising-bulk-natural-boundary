import IsingBulk.HT.Contour.OnsiteContinuation
import IsingBulk.Tail.SelectedFDiskHolomorphic

/-! The actual onsite selected integral shares the established c/N root disk,
with no global-pole exclusion premise or source estimate assumption. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set Filter Metric
open scoped Topology BigOperators

set_option maxHeartbeats 1200000 in
theorem onsite_selected_actual_holomorphic_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ : ℝ, 0 < c ∧ 0 < eps₀ ∧
        ∀ (N : ℕ) (eps : ℝ), 1 ≤ N → 0 < eps → eps < eps₀ →
          AnalyticOnNhd ℂ (onsiteContinuedSelectedIntegral N (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ) (closedBall (radialParameter d.theta eps) (c/(N:ℝ))) ∧
          (onsiteContinuedSelectedIntegral N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ
            =ᶠ[𝓝 (radialParameter d.theta eps)]
              onsiteSelectedIntegral N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ) := by
  obtain ⟨ηR,τ₀,hηR,hτ₀,hroot⟩ := selected_actual_root_disk d hcsmall
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [Real.pi_pos,d.theta_lt])
  obtain ⟨epsR,hepsR,_hepsR1,hmargin⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min ηR (Real.sin d.thetaB/4),τ₀,lt_min hηR (by positivity),hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηR' : η < ηR := hηlt.trans_le (min_le_left _ _)
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  obtain ⟨cR,epsA,_a,hcR,hepsA,_ha,hR⟩ := hroot η α τ hη hηR' hα hαsmall hτ hτlt
  let c := min (cR/2) (1/4:ℝ)
  have hc : 0 < c := lt_min (half_pos hcR) (by norm_num)
  have hcR' : 2*c ≤ cR := by have hh := min_le_left (cR/2) (1/4:ℝ); linarith
  have hcquarter : c ≤ 1/4 := min_le_right _ _
  refine ⟨c,min epsA epsR,hc,lt_min hepsA hepsR,?_⟩
  intro N eps hN heps hepslt
  have hepsA' : eps < epsA := hepslt.trans_le (min_le_left _ _)
  have hepsR' : eps < epsR := hepslt.trans_le (min_le_right _ _)
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s₀ := radialParameter d.theta eps
  let U := ball s₀ (2*c/(N:ℝ))
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos d.c₀_pos heps]
  have hrad : 2*c/(N:ℝ) ≤ cR/(N:ℝ) := div_le_div_of_nonneg_right hcR' hn0.le
  have hroots (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ)) :=
    hR N eps θ s hN heps hepsA' hθ.1 hθ.2
      ((show ‖s-s₀‖ < 2*c/(N:ℝ) from by simpa only [U,mem_ball,dist_eq_norm] using hs).le.trans hrad)
  have hS : ∀ s ∈ U, s ≠ 0 := by
    intro s hs
    have hdist : ‖s-s₀‖ < 2*c/(N:ℝ) := by simpa only [U,mem_ball,dist_eq_norm] using hs
    have hhalf : ‖s-s₀‖ < (1:ℝ)/2 := by
      have hh : 2*c/(N:ℝ) ≤ 2*c := div_le_self (by positivity) hn
      linarith
    have hnorm : 1 ≤ ‖s₀‖ := by rw [radialParameter_norm heps.le]; linarith
    have hsn := norm_ge_half_of_near_unit hnorm hhalf
    exact norm_pos_iff.mp (by linarith)
  have hhol := onsite_continuedSelectedIntegral_analyticOn_of_roots N f hr.ne' τ
    (periodicUpperP_smooth α) (periodicLowerM_smooth d.thetaB η) (periodicUpperA_smooth α).continuous
    isOpen_ball hS (fun s hs θ hθ => (hroots s hs θ hθ).2.1)
  constructor
  · exact hhol.mono (closedBall_subset_ball (show c/(N:ℝ)<2*c/(N:ℝ) from (div_lt_div_iff_of_pos_right hn0).mpr (by linarith)))
  · have hmarg : r⁻¹-r < (sourceS s₀).im := by
      have hh := radialRadius_parameter_margin heps (hmargin eps heps hepsR')
      change r⁻¹-r+Real.sin d.theta*eps < (sourceS s₀).im at hh
      linarith [mul_pos hsint heps]
    apply onsite_continuedSelectedIntegral_eventually_original N (by omega) f hr hr1 hτ.le hmarg
    · intro x
      exact (thresholdStep_range _ _ _).1
    · intro x
      exact Real.smoothTransition.nonneg _
    · intro x hx
      exact thresholdStep_zero (by linarith) (by linarith)
    · intro x hx
      exact lowerM_zero_of_nonneg_sine d.thetaB η x hsinb hη hηsmall hx

/-- Cauchy's inequality is applied to the complete continued F integral;
its original radial derivative is identified by the proved germ equality. -/
theorem onsite_selectedIntegral_iteratedDeriv_cauchy {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (r τ : ℝ) {s₀ : ℂ} {c B : ℝ} (hc : 0 < c)
    (hhol : AnalyticOnNhd ℂ (onsiteContinuedSelectedIntegral N f r τ) (closedBall s₀ (c/(N:ℝ))))
    (hagree : onsiteContinuedSelectedIntegral N f r τ =ᶠ[𝓝 s₀] onsiteSelectedIntegral N f r τ)
    (hbound : ∀ s ∈ closedBall s₀ (c/(N:ℝ)), ‖onsiteContinuedSelectedIntegral N f r τ s‖ ≤ B)
    (j : ℕ) :
    ‖iteratedDeriv j (onsiteSelectedIntegral N f r τ) s₀‖ ≤
      (j.factorial:ℝ)*((N:ℝ)/c)^j*B := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [← hagree.iteratedDeriv_eq j]
  have hh := cauchy_bound_on_subdisk hhol hbound (div_pos hc hn) (Subset.rfl) j
  have he : ((N:ℝ)/c)^j*(c/(N:ℝ))^j=1 := by
    rw [← mul_pow]
    have hrat : ((N:ℝ)/c)*(c/(N:ℝ))=1 := by field_simp
    rw [hrat,one_pow]
  convert hh using 1
  field_simp
  linear_combination B*he

end
end IsingBulk.HT.Contour
