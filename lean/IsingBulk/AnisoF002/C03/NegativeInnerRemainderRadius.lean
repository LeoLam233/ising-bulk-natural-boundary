import IsingBulk.AnisoF002.C03.NegativeInnerRemainder

/-! # Actual inner remainder in any prescribed common analytic neighborhood

The cutoff is refined together with the radius, so the same physical
moving pole remains inside the chosen disk.  This radius refinement is
used to intersect the exact pole construction with the genuine joint
angular continuity neighborhood before any particle number is selected.
The prior verified theorem and source remain unchanged.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_actual_inner_density_remainders_below {b B : ℂ → ℂ} {φ : ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s M kappa : ℝ, 0 < r ∧ r ≤ ε ∧ 0 < s ∧ 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, 0 < n → ∃ P : (Fin n → ℝ) → ℂ,
        ContinuousOn P {q | angularShortSquare q ≤ s} ∧
        ∀ q : Fin n → ℝ, angularShortSquare q ≤ s →
          let H := fun t => completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ))
          let F := realPhaseAverage B φ n q
          let rem := dslope (filledPoleNumerator H F n (P q)) (P q)
          F (P q) = 0 ∧ ‖P q‖ ≤ r / (4 * (n : ℝ)) ∧
          deriv (realPhaseTotal B φ n q) (P q) ≠ 0 ∧
          AnalyticOnNhd ℂ rem (Metric.ball (0 : ℂ) (r / (n : ℝ))) ∧
          (∀ t ∈ Metric.ball (0 : ℂ) (r / (4 * (n : ℝ))),
            ‖rem t‖ ≤ M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖) ∧
          (Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
            ∀ t : ℂ, t ≠ P q →
              H t * phaseSiteFactor (realPhaseTotal B φ n q t) =
                (2 * H (P q) / deriv (realPhaseTotal B φ n q) (P q)) / (t - P q) + rem t) := by
  obtain ⟨R, s₀, C, a, hR, hs₀, hC, _, ha, hdata⟩ :=
    exists_actual_inner_pole_data hB hφ hπ hBi
  obtain ⟨rH, M₀, kappa, hrH, hM₀, hk, hnum⟩ :=
    exists_actual_numerator_gaussian_control hb hB hφ hπ hBi hbsq
  obtain ⟨ρ, hρ, hexp⟩ := exists_exponential_dslope_control
  let r := min ε (min R (min rH (ρ / (4 * ‖a‖))))
  have haN : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < r := lt_min hε (lt_min hR (lt_min hrH (by positivity)))
  have hrε : r ≤ ε := min_le_left _ _
  have hrR : r ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hrrH : r ≤ rH := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrρ : r ≤ ρ / (4 * ‖a‖) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let s := min s₀ (r / (4 * C))
  have hs : 0 < s := lt_min hs₀ (by positivity)
  have hss₀ : s ≤ s₀ := min_le_left _ _
  have hsC : C * s ≤ r / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp (min_le_right s₀ (r / (4 * C)))
    dsimp [s]
    nlinarith
  let M := 48 * M₀ / (‖a‖ * r)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨r, s, M, kappa, hr, hrε, hs, hM, hk, ?_⟩
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨d⟩ := hdata n hn
  refine ⟨d.pole, d.pole_continuous.mono (fun q hq => hq.trans hss₀), ?_⟩
  intro q hq
  let H := fun t => completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ))
  let F := realPhaseAverage B φ n q
  let P := d.pole q
  let E := M₀ * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hq₀ : angularShortSquare q ≤ s₀ := hq.trans hss₀
  have hradle : r / (n : ℝ) ≤ r := div_le_self hr.le hn1
  have hsub : Metric.ball (0 : ℂ) (r / (n : ℝ)) ⊆ Metric.closedBall (0 : ℂ) R :=
    fun t ht => Metric.closedBall_subset_closedBall (hradle.trans hrR) (Metric.ball_subset_closedBall ht)
  have hsubH : Metric.ball (0 : ℂ) (r / (n : ℝ)) ⊆ Metric.closedBall (0 : ℂ) rH :=
    fun t ht => Metric.closedBall_subset_closedBall (hradle.trans hrrH) (Metric.ball_subset_closedBall ht)
  have hP : ‖P‖ ≤ r / (4 * (n : ℝ)) := by
    calc
      ‖P‖ ≤ C * angularShortSquare q / (n : ℝ) := d.pole_bound q hq₀
      _ ≤ C * s / (n : ℝ) := by gcongr
      _ ≤ (r / 4) / (n : ℝ) := by gcongr
      _ = _ := by ring
  have hPa : P ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hh : r / (4 * (n : ℝ)) ≤ r / (n : ℝ) := by
      rw [show r / (4 * (n : ℝ)) = (r / (n : ℝ)) / 4 by ring]
      exact div_le_self (div_nonneg hr.le hnR.le) (by norm_num)
    exact hP.trans (hh.trans (hradle.trans hrR))
  have hF0 : F P = 0 := d.pole_zero q hq₀
  have hFa : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) (r / (n : ℝ))) :=
    (d.average_analytic q hq₀).mono hsub
  have hHa : AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) (r / (n : ℝ))) :=
    fun t ht => (hnum n q t (hsubH ht)).1
  have hcontrol (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (n : ℝ))) :
      ‖H t‖ ≤ E ∧ ‖a‖ / 2 ≤ ‖dslope F P t‖ ∧
        ‖Complex.exp (-((n : ℂ) * F t))‖ ≤ 2 ∧
        1 / 2 ≤ ‖dslope Complex.exp 0 (-((n : ℂ) * F t))‖ := by
    obtain ⟨hlo, hup, _⟩ := d.factor_bounds q hq₀ t (hsub ht)
    have htN : ‖t‖ ≤ r / (n : ℝ) := by
      simpa only [dist_zero_right] using (Metric.mem_ball.mp ht).le
    have hdiff : ‖t - P‖ ≤ 5 * r / (4 * (n : ℝ)) := by
      calc
        ‖t - P‖ ≤ ‖t‖ + ‖P‖ := norm_sub_le t P
        _ ≤ r / (n : ℝ) + r / (4 * (n : ℝ)) := add_le_add htN hP
        _ = _ := by ring
    have hF : F t = (t - P) * dslope F P t := by
      simpa only [hF0, sub_zero, smul_eq_mul] using (sub_smul_dslope F P t).symm
    have harg : -((n : ℂ) * F t) ∈ Metric.closedBall (0 : ℂ) ρ := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_mul, norm_natCast,
        hF, norm_mul]
      calc
        _ ≤ (n : ℝ) * (5 * r / (4 * (n : ℝ)) * (3 * ‖a‖ / 2)) := by gcongr
        _ = 15 * r * ‖a‖ / 8 := by field_simp; ring
        _ ≤ ρ := by
          have hh := (le_div_iff₀ (by positivity : 0 < 4 * ‖a‖)).mp hrρ
          nlinarith
    have he := hexp _ harg
    exact ⟨(hnum n q t (hsubH ht)).2, hlo, he.2.2.2, he.2.1⟩
  obtain ⟨hRa, hRb⟩ := filledPoleNumerator_remainder_bound hn hr haN hE hHa hFa hP hcontrol
  have hFdiff : DifferentiableAt ℂ F P := (d.average_analytic q hq₀ P hPa).differentiableAt
  have hD : deriv (realPhaseTotal B φ n q) P = (n : ℂ) * deriv F P :=
    realPhaseTotal_deriv B φ hn q P hFdiff
  have hD0 : deriv (realPhaseTotal B φ n q) P ≠ 0 := by
    rw [hD]
    apply mul_ne_zero hn0
    have hh : dslope F P P ≠ 0 := (d.factor_bounds q hq₀ P hPa).2.2
    simpa only [dslope_same] using hh
  refine ⟨hF0, hP, hD0, hRa, ?_, ?_⟩
  · intro t ht
    calc
      _ ≤ 48 * E / (‖a‖ * r) := hRb t ht
      _ = _ := by dsimp [E, M]; ring
  · intro hres t ht
    rw [realPhaseTotal_eq_average B φ hn q t, hD]
    exact full_site_factor_exact_pole_remainder H F n ((n : ℂ) * ((φ : ℂ) * Complex.I)) P t
      hF0 hres ht


end
end IsingBulk.AnisoF002.NegativeHT
