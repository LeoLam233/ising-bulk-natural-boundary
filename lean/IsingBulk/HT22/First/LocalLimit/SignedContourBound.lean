import IsingBulk.HT22.First.LocalLimit.SignedNonresonantChart

/-! The genuine physical density on a fixed balanced complex angular chart:
compact upper-sheet geometry, rather than derivative estimates, suffices to
identify the local germ and bound every fixed radial derivative. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Branch
open IsingBulk.Preferred22
open scoped Topology BigOperators

theorem compact_contour_upper_eventually {n N : ℕ} (K : Set (Fin n → ℝ))
    (hK : IsCompact K) (ψ : (Fin n → ℝ) → (Fin N → ℂ)) (hψ : Continuous ψ)
    (s : ℂ) (hs : s≠0)
    (hW : ∀ x∈K,∀ i,0<(temperatureTrace s-Complex.cos (ψ x i)).im) :
    ∀ᶠ t in 𝓝 s,∀ x∈K,∀ i,0<(temperatureTrace t-Complex.cos (ψ x i)).im := by
  have hSc : ContinuousAt temperatureTrace s := continuousAt_id.add (continuousAt_id.inv₀ hs)
  have hi (i : Fin N) : ∀ᶠ t in 𝓝 s,∀ x∈K,0<(temperatureTrace t-Complex.cos (ψ x i)).im := by
    rcases K.eq_empty_or_nonempty with hKe | hKn
    · subst K
      exact Eventually.of_forall (fun _ _ hx => False.elim hx)
    have hc : Continuous (fun x => (Complex.cos (ψ x i)).im) :=
      continuous_im.comp (Complex.continuous_cos.comp ((continuous_apply i).comp hψ))
    obtain ⟨x₀,hx₀,hmax⟩ := hK.exists_isMaxOn hKn hc.continuousOn
    have hpos : (Complex.cos (ψ x₀ i)).im < (temperatureTrace s).im := by
      have hh := hW x₀ hx₀ i
      simpa only [sub_im,sub_pos] using hh
    have hev := (continuous_im.continuousAt.comp hSc).eventually (Ioi_mem_nhds hpos)
    filter_upwards [hev] with t ht
    intro x hx
    have hh : (Complex.cos (ψ x i)).im≤(Complex.cos (ψ x₀ i)).im := hmax hx
    change (Complex.cos (ψ x₀ i)).im<(temperatureTrace t).im at ht
    change 0<(temperatureTrace t).im-(Complex.cos (ψ x i)).im
    linarith
  filter_upwards [Filter.eventually_all.mpr hi] with t ht
  exact fun x hx i => ht i x hx

theorem signed_local_contour_derivatives_bounded {n N : ℕ} (negative : Bool) (θ μ β : ℝ)
    (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N≠0)
    (ψ : (Fin n → ℝ) → (Fin N → ℂ)) (hψ : Continuous ψ)
    (hψ0 : ψ 0=fun _ => (μ:ℂ)) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ, Continuous χ →
      (∀ x,χ x≠0 → ‖x‖<R) →
      ∀ εU : ℝ,0<εU →
      (∀ ε : ℝ,0<ε → ε<εU → ∀ x,‖x‖≤R → ∀ i,
        0<(temperatureTrace (radialParameter θ ε)-Complex.cos (ψ x i)).im) →
      ∀ j : ℕ,∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖(deriv^[j] (fun t => ∫ x,χ x*Physical.complexSignedDensity negative (t,ψ x)))
          (radialParameter θ ε)‖≤C := by
  obtain ⟨R,hR,hI⟩ := signed_local_integral_analyticAt negative θ μ β hβ hβπ hrel hgap ψ hψ hψ0
  refine ⟨R,hR,?_⟩
  intro χ hχ hχs εU hεU hW j
  let F := fun t => ∫ x,χ x*signedPhaseDensity negative (t,ψ x)
  have hf : AnalyticAt ℂ F (exp ((θ:ℂ)*I)) := hI χ hχ hχs
  have hd : ∀ k : ℕ,AnalyticAt ℂ (deriv^[k] F) (exp ((θ:ℂ)*I)) := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih => rw [Function.iterate_succ_apply'];exact ih.deriv
  have hrad : Tendsto (radialParameter θ) (𝓝[>] 0) (𝓝 (exp ((θ:ℂ)*I))) := by
    have hcont : Continuous (radialParameter θ) := by unfold radialParameter;fun_prop
    simpa [radialParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  let C := ‖(deriv^[j] F) (exp ((θ:ℂ)*I))‖+1
  have hC : 0<C := by dsimp [C];positivity
  have hev := ((hd j).continuousAt.tendsto.comp hrad).norm.eventually (Iio_mem_nhds (show
    ‖(deriv^[j] F) (exp ((θ:ℂ)*I))‖<C by dsimp [C];linarith))
  obtain ⟨ε₀,hε₀,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨C,min ε₀ εU,hC,lt_min hε₀ hεU,?_⟩
  intro ε he he0
  have heU := he0.trans_le (min_le_right _ _)
  have heB := he0.trans_le (min_le_left _ _)
  have hs0 : radialParameter θ ε≠0 := by
    apply norm_ne_zero_iff.mp
    rw [radialParameter_norm he.le]
    positivity
  have hupper := compact_contour_upper_eventually (Metric.closedBall (0:Fin n → ℝ) R)
    (isCompact_closedBall _ _) ψ hψ (radialParameter θ ε) hs0
    (fun x hx i => hW ε he heU x (by simpa only [mem_closedBall,dist_zero_right] using hx) i)
  have heq := signed_weighted_integral_deriv_eq_phase negative χ ψ (radialParameter θ ε)
    (hupper.mono (fun t ht x hx => ht x (mem_closedBall_zero_iff.mpr (hχs x hx).le))) j
  rw [heq]
  exact (hbound ⟨he,heB⟩).le

end
end IsingBulk.HT22.LocalLimit
