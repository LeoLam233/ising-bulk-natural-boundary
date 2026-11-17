import IsingBulk.AnisoF002.C03.NegativeCurvatureRatio
import IsingBulk.AnisoF002.C03.NegativeGlobalPhase

/-!
# The actual all-winding expansion at the common angular center

At angular center zero the exact evenness of the phase kills the linear
term for every tuple, without a zero-sum assumption.  The full quartic
error is retained.  The actual unsquared dispersion fixes the leading
quadratic coefficient to minus one half of the temperature derivative.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem angularJet_one_zero_of_even {g : ℂ × ℂ → ℂ} {t : ℂ}
    (hg : AnalyticAt ℂ g (t, 0)) (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) :
    angularJet 1 g (t, 0) = 0 := by
  have hd : DifferentiableAt ℂ (fun d : ℂ => g (t, d)) 0 :=
    (hg.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  simpa only [angularJet, iteratedDeriv_one] using deriv_zero_of_even hd (heven t)

theorem full_even_center_angular_remainder {g : ℂ × ℂ → ℂ} {r M : ℝ}
    (hM : 0 ≤ M) (ha : AnalyticOnNhd ℂ g (Metric.ball (0, 0) r))
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d))
    (hfour : ∀ p ∈ Metric.ball (0, 0) r, ‖angularJet 4 g p‖ ≤ M)
    (hthree : ∀ t d : ℂ, (t, d) ∈ Metric.ball (0, 0) r →
      ‖angularJet 3 g (t, d)‖ ≤ M * ‖d‖)
    (n : ℕ) {t : ℂ} {v : Fin n → ℂ}
    (hp : (t, (0 : ℂ)) ∈ Metric.ball (0, 0) r)
    (hv : ∀ i, (t, v i) ∈ Metric.ball (0, 0) r) :
    ‖(∑ i, g (t, v i)) - (n : ℂ) * g (t, 0) -
      (angularJet 2 g (t, 0) / 2) * (∑ i, v i ^ 2)‖ ≤ M * ∑ i, ‖v i‖ ^ 4 := by
  have hz := angularJet_one_zero_of_even (ha _ hp) heven
  have he : (∑ i, g (t, v i)) - (n : ℂ) * g (t, 0) -
      (angularJet 2 g (t, 0) / 2) * (∑ i, v i ^ 2) =
      ∑ i, (g (t, v i) - g (t, 0) - (angularJet 2 g (t, 0) / 2) * v i ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ i, ‖g (t, v i) - g (t, 0) - (angularJet 2 g (t, 0) / 2) * v i ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ i, M * ‖v i‖ ^ 4 := Finset.sum_le_sum fun i _ => by
      simpa only [zero_add, hz, zero_mul, sub_zero, norm_zero, zero_mul, zero_add] using
        angular_quadratic_remainder hM ha hfour hthree hp
          (show (t, (0 : ℂ) + v i) ∈ Metric.ball (0, 0) r by simpa using hv i)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exists_uniform_all_angle_center_expansion {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ n : ℕ, ∀ t : ℂ, ∀ v : Fin n → ℂ,
      (t, (0 : ℂ)) ∈ Metric.ball (0, 0) r →
      (∀ i, (t, v i) ∈ Metric.ball (0, 0) r) →
      ‖(∑ i, g (t, v i)) - (n : ℂ) * g (0, 0) -
        (n : ℂ) * phaseTemperatureDerivative g (0, 0) * t -
        (angularJet 2 g (0, 0) / 2) * (∑ i, v i ^ 2)‖ ≤
        M * ((n : ℝ) * ‖t‖ ^ 2 + ‖t‖ * displacementSquare n v + ∑ i, ‖v i‖ ^ 4) := by
  obtain ⟨r₀, M₀, hr₀, hM₀, _, _, hquad⟩ := analytic_joint_uniform_estimates hg
  obtain ⟨r₁, M₁, hr₁, hM₁, ha, hfour, hjet, hthree⟩ :=
    exists_uniform_even_angular_jet_bounds hg heven
  let r := min r₀ r₁
  let M := M₀ + M₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hM : 0 < M := by dsimp [M]; positivity
  have hM₀' : M₀ ≤ M := by dsimp [M]; linarith
  have hM₁' : M₁ ≤ M := by dsimp [M]; linarith
  have hs₀ : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hs₁ : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨r, M, hr, hM, ?_⟩
  intro n t v ht hv
  have h0 : ((0 : ℂ), (0 : ℂ)) ∈ Metric.ball (0, 0) r := Metric.mem_ball_self hr
  have hh := full_phase_expansion_of_estimates n g 0 0 t v M hM.le
  have hang : ‖(∑ i, g (t, (0 : ℂ) + v i)) - (n : ℂ) * g (t, 0) -
      (angularJet 2 g (t, 0) / 2) * (∑ i, v i ^ 2)‖ ≤
      M * (‖(0 : ℂ)‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4) := by
    simpa only [zero_add, norm_zero, zero_mul] using
      (full_even_center_angular_remainder hM₁.le ha heven hfour hthree n
        (hs₁ ht) (fun i => hs₁ (hv i))).trans
          (mul_le_mul_of_nonneg_right hM₁' (Finset.sum_nonneg fun i _ => by positivity))
  have htime : ‖g (t, 0) - g (0, 0) - phaseTemperatureDerivative g (0, 0) * (t - 0)‖ ≤
      M * ‖t - 0‖ ^ 2 := by
    have hq := hquad (0, 0) (hs₀ h0) (t, 0) (hs₀ ht)
    have hlin : fderiv ℂ g (0, 0) ((t, 0) - (0, 0)) =
        phaseTemperatureDerivative g (0, 0) * t := by
      have he : (t, (0 : ℂ)) - (0, 0) = t • ((1, 0) : ℂ × ℂ) := by ext <;> simp
      rw [he, map_smul, smul_eq_mul, mul_comm]
      rfl
    rw [hlin] at hq
    have hq' : ‖g (t, 0) - g (0, 0) - phaseTemperatureDerivative g (0, 0) * t‖ ≤ M₀ * ‖t‖ ^ 2 := by
      simpa [Prod.norm_def] using hq
    simpa only [sub_zero] using hq'.trans (mul_le_mul_of_nonneg_right hM₀' (sq_nonneg _))
  have hsecond : ‖angularJet 2 g (t, 0) - angularJet 2 g (0, 0)‖ ≤ M * ‖t - 0‖ :=
    (hjet 0 0 t (hs₁ h0) (hs₁ ht)).trans
      (mul_le_mul_of_nonneg_right hM₁' (norm_nonneg _))
  simpa only [zero_add, sub_zero, norm_zero, zero_mul, add_zero] using hh hang htime hsecond

theorem actual_negative_center_second_jet {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    angularJet 2 (negativeGlobalPhase B φ) (0, 0) =
      -phaseTemperatureDerivative (negativeGlobalPhase B φ) (0, 0) := by
  have hs : Real.sin φ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hφ hπ).ne'
  have hB0 : B 0 ≠ 0 := by intro h; simp [h] at hBi
  have ha := negativeGlobalPhase_analyticAt_zero hB hφ hπ
  have hc : negativeGlobalPhase B φ (0, 0) = (φ : ℂ) * Complex.I := by
    simpa using negativeGlobalPhase_center B hφ hπ (0 : ℂ)
  have hr := negative_center_angular_ratio B φ 0 hs
    (by simpa using hB) (by simpa using hB0)
    (by simpa using ha) (by simpa using hc)
    (Eventually.of_forall (negativeGlobalPhase_cosh B φ))
  have hd : phaseTemperatureDerivative (negativeGlobalPhase B φ) (0, 0) ≠ 0 :=
    physical_negative_phase_temperature_derivative_ne_zero hs hB hB0 ha hc
      (Eventually.of_forall (negativeGlobalPhase_cosh B φ))
  simp only [Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
    sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at hr
  field_simp at hr
  exact hr

end
end IsingBulk.AnisoF002.NegativeHT
