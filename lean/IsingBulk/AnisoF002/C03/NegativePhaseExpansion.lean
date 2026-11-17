import IsingBulk.AnisoF002.C03.NegativePhaseTaylor

/-!
# Dimension-uniform full phase remainder

This is the full Taylor estimate immediately preceding frozen F002 (4.8).
Temperature, second-angular-jet transport, cubic and quartic errors are
all retained.  No particle or angular term is discarded.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology BigOperators

theorem norm_sum_squares_le_displacement (n : ℕ) (v : Fin n → ℂ) :
    ‖∑ i, v i ^ 2‖ ≤ displacementSquare n v := by
  apply (norm_sum_le Finset.univ (fun i => v i ^ 2)).trans
  apply Finset.sum_le_sum
  intro i _
  exact le_of_eq (norm_pow (v i) 2)

theorem full_phase_expansion_of_estimates
    (n : ℕ) (g : ℂ × ℂ → ℂ) (τ d t : ℂ) (v : Fin n → ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (ha : ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (t, d) -
      (angularJet 2 g (t, d) / 2) * (∑ i, v i ^ 2)‖ ≤
        M * (‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4))
    (ht : ‖g (t, d) - g (τ, d) - phaseTemperatureDerivative g (τ, d) * (t - τ)‖ ≤
      M * ‖t - τ‖ ^ 2)
    (hj : ‖angularJet 2 g (t, d) - angularJet 2 g (τ, d)‖ ≤ M * ‖t - τ‖) :
    ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (τ, d) -
      (n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) -
      (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)‖ ≤
      M * ((n : ℝ) * ‖t - τ‖ ^ 2 + ‖t - τ‖ * displacementSquare n v +
        ‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4) := by
  have htime : ‖(n : ℂ) *
      (g (t, d) - g (τ, d) - phaseTemperatureDerivative g (τ, d) * (t - τ))‖ ≤
      (n : ℝ) * (M * ‖t - τ‖ ^ 2) := by
    rw [norm_mul, show ‖(n : ℂ)‖ = (n : ℝ) by simp]
    exact mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
  have hjet : ‖((angularJet 2 g (t, d) - angularJet 2 g (τ, d)) / 2) *
      (∑ i, v i ^ 2)‖ ≤ M * ‖t - τ‖ * displacementSquare n v := by
    rw [norm_mul, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    have hcoef : ‖angularJet 2 g (t, d) - angularJet 2 g (τ, d)‖ / 2 ≤ M * ‖t - τ‖ :=
      (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans hj
    exact mul_le_mul hcoef (norm_sum_squares_le_displacement n v)
      (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
  calc
    _ = ‖((∑ i, g (t, d + v i)) - (n : ℂ) * g (t, d) -
        (angularJet 2 g (t, d) / 2) * (∑ i, v i ^ 2)) +
        (n : ℂ) * (g (t, d) - g (τ, d) - phaseTemperatureDerivative g (τ, d) * (t - τ)) +
        ((angularJet 2 g (t, d) - angularJet 2 g (τ, d)) / 2) * (∑ i, v i ^ 2)‖ := by
      congr 1
      ring
    _ ≤ ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (t, d) -
        (angularJet 2 g (t, d) / 2) * (∑ i, v i ^ 2)‖ +
        ‖(n : ℂ) * (g (t, d) - g (τ, d) - phaseTemperatureDerivative g (τ, d) * (t - τ))‖ +
        ‖((angularJet 2 g (t, d) - angularJet 2 g (τ, d)) / 2) * (∑ i, v i ^ 2)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * (‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4) +
        (n : ℝ) * (M * ‖t - τ‖ ^ 2) + M * ‖t - τ‖ * displacementSquare n v :=
      add_le_add (add_le_add ha htime) hjet
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem exists_uniform_full_phase_expansion {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ n : ℕ, ∀ τ d t : ℂ, ∀ v : Fin n → ℂ,
        (∑ i, v i) = 0 → (τ, d) ∈ Metric.ball (0, 0) r →
        (t, d) ∈ Metric.ball (0, 0) r →
        (∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r) →
        ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (τ, d) -
          (n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) -
          (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)‖ ≤
          M * ((n : ℝ) * ‖t - τ‖ ^ 2 + ‖t - τ‖ * displacementSquare n v +
            ‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4) := by
  obtain ⟨r₀, M₀, hr₀, hM₀, _, _, hquad⟩ := analytic_joint_uniform_estimates hg
  obtain ⟨r₁, M₁, hr₁, hM₁, ha, hfour, hjet, hthree⟩ :=
    exists_uniform_even_angular_jet_bounds hg heven
  let r := min r₀ r₁
  let M := M₀ + M₁
  have hM : 0 < M := by dsimp [M]; positivity
  have hM₀' : M₀ ≤ M := by dsimp [M]; linarith
  have hM₁' : M₁ ≤ M := by dsimp [M]; linarith
  have hs₀ : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hs₁ : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨r, M, lt_min hr₀ hr₁, hM, ?_⟩
  intro n τ d t v hsum hp hq hv
  apply full_phase_expansion_of_estimates n g τ d t v M hM.le
  · exact (full_phase_angular_remainder hM₁.le ha hfour hthree n hsum (hs₁ hq)
      (fun i => hs₁ (hv i))).trans (mul_le_mul_of_nonneg_right hM₁' (by positivity))
  · have hh := hquad (τ, d) (hs₀ hp) (t, d) (hs₀ hq)
    have hlin : fderiv ℂ g (τ, d) ((t, d) - (τ, d)) =
        phaseTemperatureDerivative g (τ, d) * (t - τ) := by
      have hdiff : (t, d) - (τ, d) = (t - τ) • ((1, 0) : ℂ × ℂ) := by ext <;> simp
      rw [hdiff, map_smul, smul_eq_mul, mul_comm]
      rfl
    rw [hlin] at hh
    have htime : ‖g (t, d) - g (τ, d) - phaseTemperatureDerivative g (τ, d) * (t - τ)‖ ≤
        M₀ * ‖t - τ‖ ^ 2 := by simpa [Prod.norm_def] using hh
    exact htime.trans (mul_le_mul_of_nonneg_right hM₀' (sq_nonneg _))
  · exact (hjet τ d t (hs₁ hp) (hs₁ hq)).trans
      (mul_le_mul_of_nonneg_right hM₁' (norm_nonneg _))

end
end IsingBulk.AnisoF002.NegativeHT
