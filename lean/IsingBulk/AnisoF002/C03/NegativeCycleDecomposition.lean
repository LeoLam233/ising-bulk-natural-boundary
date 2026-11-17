import IsingBulk.AnisoF002.C03.NegativeCyclePoleJets
import IsingBulk.AnisoF002.C03.NegativeOuterCycleRemainder

/-!
# Exact decomposition of the original complete resonant coefficient

This is an identity on a genuine coefficient disk.  Both analytic
remainders are the actual fixed-cutoff integrals, and the retained pole
integral uses the complete physical residue over every inner winding.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

theorem negativePhysicalCoefficient_eq_real_density (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (t : ℂ) :
    negativePhysicalCoefficient b B φ n t =
      ∫ q in regularAngularBox n,
        realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q) := by
  unfold negativePhysicalCoefficient realNegativeDensity edgeSiteFactor
  simp only [realPhaseTotal_eq_edge]

set_option maxHeartbeats 1000000 in
theorem actual_coefficient_inner_outer_decomposition {b B : ℂ → ℂ}
    {φ r s M kappa c E delta : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 ≤ s) (hM : 0 ≤ M) (hc : 0 < c) (hE : 0 ≤ E)
    (hdelta : 0 < delta) (hdeltaR : delta ≤ r / (4 * (n + 1 : ℕ))) (hdeltaC : delta ≤ c / 2)
    (hres : Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1)
    (hmeas : ∀ t ∈ Metric.ball (0 : ℂ) delta, Measurable (realNegativeDensity b B φ (n + 1) t))
    (hbound : ∀ t ∈ Metric.ball (0 : ℂ) delta, ∀ q : Fin n → ℝ,
      ‖realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q)‖ ≤ E)
    (hsep : ∀ q : Fin n → ℝ, angularShortSquare (negativeConstrainedAngles q) ≤ s →
      c ≤ ‖d.pole (negativeConstrainedAngles q)‖) :
    ∀ t ∈ Metric.ball (0 : ℂ) delta,
      negativePhysicalCoefficient b B φ n t =
        innerCyclePoleIntegral d t + innerCycleRemainder d hs t + outerCycleRemainder b B φ s n t := by
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) delta := Metric.mem_ball_self hdelta
  obtain ⟨A, P, L, hL, hAm, hPm, hAb, hPb, hsame, houtside⟩ :=
    exists_inner_cycle_pole_representatives d hr hs hM hc hE hres (hmeas 0 hzero) (hbound 0 hzero) hsep
  let μ : Measure (Fin n → ℝ) := volume.restrict (regularAngularBox n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [regularAngularBox_volume]
    exact ENNReal.ofReal_ne_top)
  intro t ht
  have htc : t ∈ Metric.ball (0 : ℂ) (c / 2) := Metric.ball_subset_ball hdeltaC ht
  have htr4 : t ∈ Metric.ball (0 : ℂ) (r / (4 * (n + 1 : ℕ))) := Metric.ball_subset_ball hdeltaR ht
  have htr : t ∈ Metric.ball (0 : ℂ) (r / (n + 1 : ℕ)) :=
    Metric.ball_subset_ball (by
      have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      apply div_le_div_of_nonneg_left hr.le hN
      linarith) htr4
  let Kp : (Fin n → ℝ) → ℂ := fun q =>
    if angularShortSquare (negativeConstrainedAngles q) ≤ s then
      d.actualResidue (negativeConstrainedAngles q) / (t - d.pole (negativeConstrainedAngles q)) else 0
  let G : (Fin n → ℝ) → ℂ := fun q => d.realCycleRemainderDensity hs t (negativeConstrainedAngles q)
  let O : (Fin n → ℝ) → ℂ := fun q =>
    if s < angularShortSquare (negativeConstrainedAngles q) then
      realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q) else 0
  have hKeq (q : Fin n → ℝ) : A q / (t - P q) = Kp q := by
    by_cases hq : angularShortSquare (negativeConstrainedAngles q) ≤ s
    · simp only [Kp, hq, ↓reduceIte, (hsame q hq).1, (hsame q hq).2]
    · simp only [Kp, hq, ↓reduceIte, houtside q hq, zero_div]
  have hKi : Integrable Kp μ := by
    have hi := (integral_pole_power_hasDerivAt (μ := μ) hc hAm hPm hAb hPb 0 htc).1
    simp only [Nat.zero_add, pow_one] at hi
    exact hi.congr (Eventually.of_forall hKeq)
  have hGm : Measurable G := measurable_real_pullback
    (measurable_complex_parameter_slice (d.realCycleRemainderDensity_measurable hs) t)
    (negativeConstrainedAngles_continuous n).measurable
  have hGi : Integrable G μ := (integrable_const
      (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ‖windingNormalization (n + 1)‖)).mono'
    hGm.aestronglyMeasurable (Eventually.of_forall fun q =>
      d.realCycleRemainderDensity_bound hs hM (negativeConstrainedAngles q) htr4)
  have hOm : Measurable O := Measurable.ite
    (measurableSet_lt measurable_const (((angularShortSquare_continuous (n + 1)).comp
      (negativeConstrainedAngles_continuous n)).measurable))
    (measurable_real_pullback (hmeas t ht) (negativeConstrainedAngles_continuous n).measurable) measurable_const
  have hOi : Integrable O μ := by
    apply (integrable_const E).mono' hOm.aestronglyMeasurable
    apply Eventually.of_forall
    intro q
    dsimp [O]
    split_ifs with hq
    · exact hbound t ht q
    · simpa only [norm_zero] using hE
  have heq (q : Fin n → ℝ) : realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q) =
      Kp q + G q + O q := by
    by_cases hq : angularShortSquare (negativeConstrainedAngles q) ≤ s
    · have hne : t ≠ d.pole (negativeConstrainedAngles q) := by
        intro he
        have htNorm : ‖t‖ < c / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using htc
        rw [he] at htNorm
        linarith [hsep q hq]
      have hd := d.exact_density hres ⟨negativeConstrainedAngles q, hq⟩ t htr hne
      have ho : ¬ s < angularShortSquare (negativeConstrainedAngles q) := not_lt_of_ge hq
      dsimp [Kp, G, O]
      simp only [hq, ho, ↓reduceIte, add_zero, d.realCycleRemainderDensity_eq hs hq]
      exact hd
    · have ho : s < angularShortSquare (negativeConstrainedAngles q) := lt_of_not_ge hq
      simp only [Kp, G, O, hq, ho, ↓reduceIte, InnerRemainderFamily.realCycleRemainderDensity,
        zero_add]
  rw [negativePhysicalCoefficient_eq_real_density]
  calc
    _ = ∫ q, (Kp q + G q + O q) ∂μ := integral_congr_ae (Eventually.of_forall heq)
    _ = (∫ q, Kp q ∂μ) + (∫ q, G q ∂μ) + (∫ q, O q ∂μ) := by
      change (∫ q, ((Kp + G) + O) q ∂μ) = _
      rw [integral_add' (hKi.add hGi) hOi, integral_add' hKi hGi]
    _ = _ := rfl

theorem normalized_jets_of_three_analytic_germs {f g h k : ℂ → ℂ}
    (heq : f =ᶠ[𝓝 0] (fun t => g t + h t + k t))
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0) (hk : AnalyticAt ℂ k 0) (j : ℕ) :
    iteratedDeriv j f 0 / (j.factorial : ℂ) =
      iteratedDeriv j g 0 / (j.factorial : ℂ) +
        iteratedDeriv j h 0 / (j.factorial : ℂ) + iteratedDeriv j k 0 / (j.factorial : ℂ) := by
  rw [heq.iteratedDeriv_eq j]
  change iteratedDeriv j ((g + h) + k) 0 / (j.factorial : ℂ) = _
  rw [iteratedDeriv_add (hg.add hh).contDiffAt hk.contDiffAt,
    iteratedDeriv_add hg.contDiffAt hh.contDiffAt]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
