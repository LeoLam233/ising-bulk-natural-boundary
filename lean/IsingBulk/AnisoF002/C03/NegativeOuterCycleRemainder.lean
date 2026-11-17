import IsingBulk.AnisoF002.C03.NegativeOuterCycleControl
import IsingBulk.AnisoF002.C03.NegativeInnerCycleRemainder

/-!
# The actual complete outer-cycle analytic remainder

The complement S>s is integrated on the original independent-coordinate
torus.  Its complete density is holomorphic on a c/N disk; every fixed
Taylor order has the full Gaussian bound with the physical normalization.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

def outerCycleRemainder (b B : ℂ → ℂ) (φ s : ℝ) (n : ℕ) (t : ℂ) : ℂ :=
  ∫ q in regularAngularBox n,
    if s < angularShortSquare (negativeConstrainedAngles q) then
      realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q) else 0

def outerDensityExtension (b B : ℂ → ℂ) (φ r s : ℝ) (n : ℕ)
    (t : ℂ) (q : Fin n → ℝ) : ℂ :=
  if t ∈ Metric.ball 0 (r / (n : ℝ)) ∧ s < angularShortSquare q then
    realNegativeDensity b B φ n t q else 0

theorem outerDensityExtension_eq (b B : ℂ → ℂ) (φ r s : ℝ) (n : ℕ)
    {t : ℂ} (ht : t ∈ Metric.ball 0 (r / (n : ℝ))) (q : Fin n → ℝ) :
    outerDensityExtension b B φ r s n t q =
      if s < angularShortSquare q then realNegativeDensity b B φ n t q else 0 := by
  simp only [outerDensityExtension, ht, true_and]

theorem outerDensityExtension_measurable {b B : ℂ → ℂ} {φ r s : ℝ} {n : ℕ}
    (hc : ContinuousOn (fun p : ℂ × (Fin n → ℝ) => realNegativeDensity b B φ n p.1 p.2)
      {p | p.1 ∈ Metric.ball 0 (r / (n : ℝ)) ∧ s < angularShortSquare p.2}) :
    Measurable (Function.uncurry (outerDensityExtension b B φ r s n)) := by
  have hm : MeasurableSet {p : ℂ × (Fin n → ℝ) |
      p.1 ∈ Metric.ball 0 (r / (n : ℝ)) ∧ s < angularShortSquare p.2} :=
    ((Metric.isOpen_ball.preimage continuous_fst).inter
      (isOpen_lt continuous_const ((angularShortSquare_continuous n).comp continuous_snd))).measurableSet
  convert hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hm using 1
  rfl

set_option maxHeartbeats 1000000 in
theorem exists_actual_outer_cycle_remainders {b B : ℂ → ℂ} {φ s : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (hs : 0 < s) :
    ∃ r M kappa : ℝ, 0 < r ∧ 0 < M ∧ 0 < kappa ∧ ∀ n : ℕ,
      AnalyticOnNhd ℂ (outerCycleRemainder b B φ s n)
        (Metric.ball 0 (r / (4 * (n + 1 : ℕ)))) ∧
      (∀ t ∈ Metric.closedBall (0 : ℂ) (r / (2 * (n + 1 : ℕ))),
        ‖outerCycleRemainder b B φ s n t‖ ≤ M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      ∀ j : ℕ,
        ‖iteratedDeriv j (outerCycleRemainder b B φ s n) 0 / (j.factorial : ℂ)‖ ≤
          M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
            (r / (16 * (n + 1 : ℕ))) ^ j := by
  obtain ⟨r₀, M, kappa, hr₀, hM, hk, hden⟩ :=
    exists_actual_outer_density_control hb hB hφ hπ hBi hbsq hs
  obtain ⟨rJ, hrJ, hJ⟩ := exists_actual_joint_real_factor_control hb hB hφ hπ hBi hbsq
  obtain ⟨rp, eta, hrp, he, _, hphase⟩ := exists_actual_outer_phase_control hB hφ hπ hBi hs
  let r := min r₀ (min rJ rp)
  have hr : 0 < r := lt_min hr₀ (lt_min hrJ hrp)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrrJ : r ≤ rJ := (min_le_right _ _).trans (min_le_left _ _)
  have hrrp : r ≤ rp := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, M, kappa, hr, hM, hk, ?_⟩
  intro n
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsubJ : Metric.ball (0 : ℂ) (r / (N : ℝ)) ⊆ Metric.ball 0 rJ :=
    Metric.ball_subset_ball ((div_le_self hr.le hN1).trans hrrJ)
  have hsub₀ : Metric.closedBall (0 : ℂ) (r / (N : ℝ)) ⊆ Metric.closedBall 0 (r₀ / (N : ℝ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right hrr₀ hNR.le)
  have hsubp : Metric.closedBall (0 : ℂ) (r / (N : ℝ)) ⊆ Metric.closedBall 0 (rp / (N : ℝ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right hrrp hNR.le)
  have hGc : ContinuousOn (fun p : ℂ × (Fin N → ℝ) => realPhaseTotal B φ N p.2 p.1)
      {p | p.1 ∈ Metric.ball 0 rJ} := by
    apply (continuousOn_const.add (continuousOn_const.mul (hJ N).2.1)).congr
    intro p _
    exact realPhaseTotal_eq_average B φ hN p.2 p.1
  have hDc : ContinuousOn (fun p : ℂ × (Fin N → ℝ) => realNegativeDensity b B φ N p.1 p.2)
      {p | p.1 ∈ Metric.ball 0 (r / (N : ℝ)) ∧ s < angularShortSquare p.2} := by
    intro p hp
    have hnum := ((hJ N).1.mono (fun _ hu => hsubJ hu.1)) p hp
    have hgamma := (hGc.mono (fun _ hu => hsubJ hu.1)) p hp
    have hpos := (hphase N hN p.2 hp.2.le p.1 (hsubp (Metric.ball_subset_closedBall hp.1))).2
    have hsite : ContinuousWithinAt
        (fun w : ℂ × (Fin N → ℝ) => phaseSiteFactor (realPhaseTotal B φ N w.2 w.1))
        {w | w.1 ∈ Metric.ball 0 (r / (N : ℝ)) ∧ s < angularShortSquare w.2} p :=
      (phaseSiteFactor_analyticAt (by linarith :
        0 < (realPhaseTotal B φ N p.2 p.1).re)).continuousAt.comp_continuousWithinAt
          (f := fun w : ℂ × (Fin N → ℝ) => realPhaseTotal B φ N w.2 w.1) hgamma
    exact hnum.mul hsite
  let F : ℂ → (Fin n → ℝ) → ℂ := fun t q =>
    outerDensityExtension b B φ r s N t (negativeConstrainedAngles q)
  let R : ℝ := r / (2 * (N : ℝ))
  let E : ℝ := M * Real.exp (-kappa * (N : ℝ) ^ 2) / ‖windingNormalization N‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hsubR : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 (r / (N : ℝ)) :=
    Metric.closedBall_subset_ball (by dsimp [R]; apply div_lt_div_of_pos_left hr hNR; linarith)
  have hmF : Measurable (Function.uncurry F) := by
    change Measurable (fun p : ℂ × (Fin n → ℝ) =>
      outerDensityExtension b B φ r s N p.1 (negativeConstrainedAngles p.2))
    exact measurable_parameter_pullback (outerDensityExtension_measurable hDc)
      (negativeConstrainedAngles_continuous n).measurable
  have hFexact (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (N : ℝ))) (q : Fin n → ℝ) :
      F t q = if s < angularShortSquare (negativeConstrainedAngles q) then
        realNegativeDensity b B φ N t (negativeConstrainedAngles q) else 0 :=
    outerDensityExtension_eq b B φ r s N ht _
  have haF (q : Fin n → ℝ) : AnalyticOnNhd ℂ (fun t => F t q) (Metric.closedBall 0 R) := by
    intro t ht
    have heq : (fun u => F u q) =ᶠ[𝓝 t] (fun u =>
        if s < angularShortSquare (negativeConstrainedAngles q) then
          realNegativeDensity b B φ N u (negativeConstrainedAngles q) else 0) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hsubR ht)] with u hu
      exact hFexact u hu q
    apply AnalyticAt.congr _ heq.symm
    by_cases hq : s < angularShortSquare (negativeConstrainedAngles q)
    · simp only [hq, ↓reduceIte]
      exact (hden N hN _ hq.le t (hsub₀ (Metric.ball_subset_closedBall (hsubR ht)))).1
    · simpa only [hq, ↓reduceIte] using (analyticAt_const (v := (0 : ℂ)))
  have hbF (q : Fin n → ℝ) (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) R) : ‖F t q‖ ≤ E := by
    rw [hFexact t (hsubR ht) q]
    split_ifs with hq
    · exact (hden N hN _ hq.le t (hsub₀ (Metric.ball_subset_closedBall (hsubR ht)))).2
    · simp only [norm_zero]
      dsimp [E]
      positivity
  let μ : Measure (Fin n → ℝ) := volume.restrict (regularAngularBox n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [regularAngularBox_volume]
    exact ENNReal.ofReal_ne_top)
  have hmass : μ.real univ = (2 * Real.pi) ^ n := by
    simp only [μ, Measure.real, Measure.restrict_apply_univ, regularAngularBox_volume,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  have hIeq (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (N : ℝ))) :
      (∫ q, F t q ∂μ) = outerCycleRemainder b B φ s n t := by
    apply integral_congr_ae
    exact Eventually.of_forall (hFexact t ht)
  have hInear (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (N : ℝ))) :
      (fun u => ∫ q, F u q ∂μ) =ᶠ[𝓝 t] outerCycleRemainder b B φ s n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
    exact hIeq u hu
  have hnorm : E * μ.real univ ≤ M * Real.exp (-kappa * (N : ℝ) ^ 2) := by
    rw [hmass]
    dsimp [E, N]
    rw [windingNormalization_norm_succ]
    have hp : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
    have heq : (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
        (((n + 1).factorial : ℝ) * (2 * Real.pi) ^ n)) * (2 * Real.pi) ^ n =
        M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ((n + 1).factorial : ℝ) := by field_simp
    rw [heq]
    exact div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
  obtain ⟨hIa, hIb⟩ := analytic_integral_of_measurable_analytic_disk (μ := μ) hR hmF haF hbF
  refine ⟨?_, ?_, ?_⟩
  · have hrad : r / (4 * (n + 1 : ℕ)) = R / 2 := by dsimp [R, N]; ring
    rw [hrad]
    intro t ht
    have hts : t ∈ Metric.ball (0 : ℂ) (r / (N : ℝ)) :=
      hsubR (Metric.closedBall_subset_closedBall (half_le_self hR.le) (Metric.ball_subset_closedBall ht))
    exact (hIa t ht).congr (hInear t hts)
  · intro t ht
    rw [← hIeq t (hsubR ht)]
    exact (hIb t ht).trans hnorm
  · intro j
    have hj := measurable_analytic_integral_normalized_jets (μ := μ) hR hmF haF hbF j
    rw [(hInear 0 (Metric.mem_ball_self (div_pos hr hNR))).iteratedDeriv_eq j] at hj
    have hh := hj.trans (div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ (R / 8) ^ j))
    have hrad : r / (16 * (n + 1 : ℕ)) = R / 8 := by dsimp [R, N]; ring
    rw [hrad]
    exact hh

end
end IsingBulk.AnisoF002.NegativeHT
