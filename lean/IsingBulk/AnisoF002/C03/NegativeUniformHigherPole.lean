import IsingBulk.AnisoF002.C03.NegativeHigherPoleError

/-!
# Uniform higher pole control from one analytic even phase

The nonzero temperature derivative and every scalar Taylor constant are
constructed on one neighborhood before n.  The bound applies to the
actual phase zero supplied by the moving-pole construction.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem exists_uniform_higher_pole_error {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : phaseTemperatureDerivative g (0, 0) ≠ 0)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d))
    {C : ℝ} (hC : 0 < C) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ n : ℕ, 0 < n → ∀ τ d t : ℂ, ∀ v : Fin n → ℂ,
        (∑ i, v i) = 0 → (τ, d) ∈ Metric.ball (0, 0) r →
        (t, d) ∈ Metric.ball (0, 0) r →
        (∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r) →
        (∑ i, g (t, d + v i)) = (n : ℂ) * g (τ, d) →
        ‖t - τ‖ ≤ C * displacementSquare n v / (n : ℝ) →
        ‖d‖ ≤ Real.pi / (n : ℝ) →
        ‖t - τ + (angularJet 2 g (τ, d) / (2 * phaseTemperatureDerivative g (τ, d))) *
          ((∑ i, v i ^ 2) / (n : ℂ))‖ ≤ K / (n : ℝ) *
          ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
            displacementSquare n v ^ 2 / (n : ℝ)) := by
  obtain ⟨R, M, hR, hM, hbound⟩ := exists_uniform_full_phase_expansion hg heven
  let a : ℝ := ‖phaseTemperatureDerivative g (0, 0)‖ / 2
  have ha : 0 < a := half_pos (norm_pos_iff.mpr hc)
  have hclose : ∀ᶠ p in 𝓝 (0, 0), a < ‖phaseTemperatureDerivative g p‖ :=
    (phaseTemperatureDerivative_analyticAt hg).continuousAt.norm.eventually
      (Ioi_mem_nhds (by dsimp [a]; linarith [norm_pos_iff.mpr hc]))
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp hclose
  let r := min R s
  let K := higherPoleErrorConstant M a C
  have hrR : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hrs : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hK : 0 < K := by dsimp [K, higherPoleErrorConstant]; positivity
  refine ⟨r, K, lt_min hR hs, hK, ?_⟩
  intro n hn τ d t v hsum hp hq hv hphase hcoarse hd
  exact higher_pole_error_of_phase_expansion n hn g τ d t v M a C hM.le ha hC.le
    (hlocal (Metric.mem_ball.mp (hrs hp))).le hphase hcoarse hd
    (hbound n τ d t v hsum (hrR hp) (hrR hq) (fun i => hrR (hv i)))

theorem coarse_pole_points_in_common_ball {n : ℕ} (hn : 0 < n)
    {r σ C : ℝ} (_hr : 0 < r) (hσ : 0 < σ) (hC : 0 ≤ C)
    (hσr : σ ≤ r / 4) (hσC : C * σ ^ 2 ≤ r / 4)
    {τ d t : ℂ} {v : Fin n → ℂ}
    (hτ : ‖τ‖ < r / 4) (hd : ‖d‖ < r / 4)
    (hQ : displacementSquare n v < σ ^ 2)
    (hcoarse : ‖t - τ‖ ≤ C * displacementSquare n v / (n : ℝ)) :
    (τ, d) ∈ Metric.ball (0, 0) r ∧ (t, d) ∈ Metric.ball (0, 0) r ∧
      ∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hQt : displacementSquare n v / (n : ℝ) ≤ σ ^ 2 :=
    (div_le_self (displacementSquare_nonneg n v) hn1).trans hQ.le
  have hdist : ‖t - τ‖ ≤ r / 4 := by
    calc
      ‖t - τ‖ ≤ C * (displacementSquare n v / (n : ℝ)) := by simpa only [mul_div_assoc] using hcoarse
      _ ≤ C * σ ^ 2 := mul_le_mul_of_nonneg_left hQt hC
      _ ≤ r / 4 := hσC
  have ht : ‖t‖ < r := by
    have hh : ‖t‖ ≤ ‖t - τ‖ + ‖τ‖ := by simpa only [sub_add_cancel] using norm_add_le (t - τ) τ
    linarith
  have hvi (i : Fin n) : ‖v i‖ < σ := by
    have hi : ‖v i‖ ^ 2 ≤ displacementSquare n v :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  constructor
  · simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using
      And.intro (show ‖τ‖ < r by linarith) (show ‖d‖ < r by linarith)
  constructor
  · simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using
      And.intro ht (show ‖d‖ < r by linarith)
  intro i
  have hdi : ‖d + v i‖ < r := (norm_add_le _ _).trans_lt (by linarith [hvi i])
  simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using And.intro ht hdi

end
end IsingBulk.AnisoF002.NegativeHT
