import IsingBulk.AnisoF002.C03.NegativeNonresonantDensity
import IsingBulk.AnisoF002.C03.NegativeJointMeasurableDensity
import IsingBulk.AnisoF002.C03.NegativeInnerCycleRemainder

/-!
# All nonresonant physical coefficients are c/N analytic remainders

This integrates the complete original density over its exact constrained
real cycle.  The proof covers every nonresonant particle class and every
Taylor order, and cancels the angular volume against the literal W_N.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem exists_actual_nonresonant_coefficient_bounds {b B : ℂ → ℂ} {φ : ℝ} {p : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ r M kappa : ℝ, 0 < r ∧ 0 < M ∧ 0 < kappa ∧ ∀ n : ℕ,
      Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) ≠ 1 →
      AnalyticOnNhd ℂ (negativePhysicalCoefficient b B φ n)
        (Metric.ball 0 (r / (4 * (n + 1 : ℕ)))) ∧
      (∀ t ∈ Metric.closedBall (0 : ℂ) (r / (2 * (n + 1 : ℕ))),
        ‖negativePhysicalCoefficient b B φ n t‖ ≤ M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      ∀ j : ℕ,
        ‖iteratedDeriv j (negativePhysicalCoefficient b B φ n) 0 / (j.factorial : ℂ)‖ ≤
          M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
            (r / (16 * (n + 1 : ℕ))) ^ j := by
  obtain ⟨r₀, M, kappa, hr₀, hM, hk, hcontrol⟩ :=
    exists_actual_nonresonant_density_control hb hB hφ hπ hBi hbsq hp hperiod
  obtain ⟨rJ, hrJ, hJ⟩ := exists_actual_joint_measurable_density hb hB hφ hπ hBi hbsq
  let r := min r₀ rJ
  have hr : 0 < r := lt_min hr₀ hrJ
  refine ⟨r, M, kappa, hr, hM, hk, ?_⟩
  intro n hne
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN
  obtain ⟨J, hJm, hJe⟩ := hJ (n + 1) hN
  let F : ℂ → (Fin n → ℝ) → ℂ := fun t q => J t (negativeConstrainedAngles q)
  let R : ℝ := r / (2 * (n + 1 : ℕ))
  let E : ℝ := M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ‖windingNormalization (n + 1)‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hsubR : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 (r / (n + 1 : ℕ)) :=
    Metric.closedBall_subset_ball (by
      dsimp [R]
      apply div_lt_div_of_pos_left hr hNR
      linarith)
  have hsubJ : Metric.ball (0 : ℂ) (r / (n + 1 : ℕ)) ⊆ Metric.ball 0 rJ :=
    Metric.ball_subset_ball ((div_le_self hr.le hN1).trans (min_le_right _ _))
  have hsub₀ : Metric.closedBall (0 : ℂ) (r / (n + 1 : ℕ)) ⊆ Metric.closedBall 0 (r₀ / (n + 1 : ℕ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_left _ _) hNR.le)
  have hFm : Measurable (Function.uncurry F) := by
    change Measurable (fun p : ℂ × (Fin n → ℝ) => J p.1 (negativeConstrainedAngles p.2))
    exact measurable_parameter_pullback hJm (negativeConstrainedAngles_continuous n).measurable
  have hFe (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (n + 1 : ℕ))) (q : Fin n → ℝ) :
      F t q = realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q) := hJe t (hsubJ ht) _
  have haF (q : Fin n → ℝ) : AnalyticOnNhd ℂ (fun t => F t q) (Metric.closedBall 0 R) := by
    intro t ht
    have heq : (fun u => F u q) =ᶠ[𝓝 t] (fun u =>
        realNegativeDensity b B φ (n + 1) u (negativeConstrainedAngles q)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hsubR ht)] with u hu
      exact hFe u hu q
    exact (hcontrol (n + 1) hN hne _ t (hsub₀ (Metric.ball_subset_closedBall (hsubR ht)))).1.congr heq.symm
  have hbF (q : Fin n → ℝ) (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) R) : ‖F t q‖ ≤ E := by
    rw [hFe t (hsubR ht) q]
    exact (hcontrol (n + 1) hN hne _ t (hsub₀ (Metric.ball_subset_closedBall (hsubR ht)))).2
  let μ : Measure (Fin n → ℝ) := volume.restrict (regularAngularBox n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [regularAngularBox_volume]
    exact ENNReal.ofReal_ne_top)
  have hmass : μ.real univ = (2 * Real.pi) ^ n := by
    simp only [μ, Measure.real, Measure.restrict_apply_univ, regularAngularBox_volume,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  have hIeq (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (n + 1 : ℕ))) :
      (∫ q, F t q ∂μ) = negativePhysicalCoefficient b B φ n t := by
    change (∫ q, F t q ∂μ) = ∫ q, _ ∂μ
    apply integral_congr_ae
    apply Eventually.of_forall
    intro q
    rw [hFe t ht q]
    unfold realNegativeDensity edgeSiteFactor
    rw [realPhaseTotal_eq_edge]
  have hInear (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) (r / (n + 1 : ℕ))) :
      (fun u => ∫ q, F u q ∂μ) =ᶠ[𝓝 t] negativePhysicalCoefficient b B φ n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
    exact hIeq u hu
  have hnorm : E * μ.real univ ≤ M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hmass]
    dsimp [E]
    rw [windingNormalization_norm_succ]
    have hpπ : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
    have heq : (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
        (((n + 1).factorial : ℝ) * (2 * Real.pi) ^ n)) * (2 * Real.pi) ^ n =
        M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ((n + 1).factorial : ℝ) := by field_simp
    rw [heq]
    exact div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
  obtain ⟨hIa, hIb⟩ := analytic_integral_of_measurable_analytic_disk (μ := μ) hR hFm haF hbF
  refine ⟨?_, ?_, ?_⟩
  · have hrad : r / (4 * (n + 1 : ℕ)) = R / 2 := by dsimp [R]; ring
    rw [hrad]
    intro t ht
    have hts := hsubR (Metric.closedBall_subset_closedBall (half_le_self hR.le) (Metric.ball_subset_closedBall ht))
    exact (hIa t ht).congr (hInear t hts)
  · intro t ht
    rw [← hIeq t (hsubR ht)]
    exact (hIb t ht).trans hnorm
  · intro j
    have hj := measurable_analytic_integral_normalized_jets (μ := μ) hR hFm haF hbF j
    rw [(hInear 0 (Metric.mem_ball_self (div_pos hr hNR))).iteratedDeriv_eq j] at hj
    have hh := hj.trans (div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ (R / 8) ^ j))
    have hrad : r / (16 * (n + 1 : ℕ)) = R / 8 := by dsimp [R]; ring
    rw [hrad]
    exact hh

end
end IsingBulk.AnisoF002.NegativeHT
