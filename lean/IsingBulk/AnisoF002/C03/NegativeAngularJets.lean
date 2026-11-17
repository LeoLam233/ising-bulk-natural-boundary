import IsingBulk.AnisoF002.C03.NegativeTaylorRemainder
import IsingBulk.AnisoF002.C03.RegularParameterJets

/-!
# Actual angular jets of the single even phase

The third angular jet vanishes on the central axis by exact evenness.
Joint analyticity then gives its uniform O(d) bound, together with the
uniform fourth jet and transport of the second jet in temperature.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

def angularJet (n : ℕ) (g : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  iteratedDeriv n (fun d : ℂ => g (p.1, d)) p.2

theorem angularJet_analyticAt {g : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hg : AnalyticAt ℂ g p) (n : ℕ) : AnalyticAt ℂ (angularJet n g) p := by
  have hswap : AnalyticAt ℂ (fun q : ℂ × ℂ => g (q.2, q.1)) (p.2, p.1) :=
    hg.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl
  have hj := IsingBulk.AnisoF002.RegularTail.C03.parameterIteratedDeriv_analyticAt hswap n
  exact hj.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl

theorem angularJet_three_zero {g : ℂ × ℂ → ℂ}
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) (t : ℂ) :
    angularJet 3 g (t, 0) = 0 := by
  have he : (fun d : ℂ => g (t, -d)) = (fun d : ℂ => g (t, d)) := funext (heven t)
  have hh := iteratedDeriv_comp_neg 3 (fun d : ℂ => g (t, d)) (0 : ℂ)
  rw [he] at hh
  simp only [neg_zero, show (-1 : ℂ) ^ 3 = -1 by norm_num, neg_one_smul] at hh
  unfold angularJet
  linear_combination hh / 2

theorem exists_uniform_even_angular_jet_bounds {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) ∧
      (∀ p ∈ Metric.ball (0, 0) r, ‖angularJet 4 g p‖ ≤ M) ∧
      (∀ τ d t : ℂ, (τ, d) ∈ Metric.ball (0, 0) r → (t, d) ∈ Metric.ball (0, 0) r →
        ‖angularJet 2 g (t, d) - angularJet 2 g (τ, d)‖ ≤ M * ‖t - τ‖) ∧
      ∀ t d : ℂ, (t, d) ∈ Metric.ball (0, 0) r → ‖angularJet 3 g (t, d)‖ ≤ M * ‖d‖ := by
  obtain ⟨r₂, M₂, hr₂, hM₂, ha₂, hb₂, _⟩ := analytic_joint_uniform_estimates (angularJet_analyticAt hg 2)
  obtain ⟨r₃, M₃, hr₃, hM₃, ha₃, hb₃, _⟩ := analytic_joint_uniform_estimates (angularJet_analyticAt hg 3)
  let M₄ : ℝ := ‖angularJet 4 g (0, 0)‖ + 1
  have hM₄ : 0 < M₄ := by dsimp [M₄]; positivity
  have hb₄ : ∀ᶠ p in 𝓝 (0, 0), ‖angularJet 4 g p‖ < M₄ :=
    (angularJet_analyticAt hg 4).continuousAt.norm.eventually
      (Iio_mem_nhds (by dsimp [M₄]; linarith))
  obtain ⟨r₄, hr₄, hh₄⟩ := Metric.eventually_nhds_iff.mp (hg.eventually_analyticAt.and hb₄)
  let r : ℝ := min r₂ (min r₃ r₄)
  let M : ℝ := M₂ + M₃ + M₄
  have hr : 0 < r := lt_min hr₂ (lt_min hr₃ hr₄)
  have hM : 0 < M := by dsimp [M]; positivity
  have h₂ : r ≤ r₂ := min_le_left _ _
  have h₃ : r ≤ r₃ := (min_le_right _ _).trans (min_le_left _ _)
  have h₄ : r ≤ r₄ := (min_le_right _ _).trans (min_le_right _ _)
  have hM₂' : M₂ ≤ M := by dsimp [M]; linarith
  have hM₃' : M₃ ≤ M := by dsimp [M]; linarith
  have hM₄' : M₄ ≤ M := by dsimp [M]; linarith
  refine ⟨r, M, hr, hM,
    (fun p hp => (hh₄ (Metric.mem_ball.mp (Metric.ball_subset_ball h₄ hp))).1),
    (fun p hp => (hh₄ (Metric.mem_ball.mp (Metric.ball_subset_ball h₄ hp))).2.le.trans hM₄'), ?_, ?_⟩
  · intro τ d t hp hq
    have hh := (convex_ball (0 : ℂ × ℂ) r₂).norm_image_sub_le_of_norm_fderiv_le
      (fun p hp' => (ha₂ p hp').differentiableAt) hb₂
      (Metric.ball_subset_ball h₂ hp) (Metric.ball_subset_ball h₂ hq)
    have ht : ‖angularJet 2 g (t, d) - angularJet 2 g (τ, d)‖ ≤ M₂ * ‖t - τ‖ := by
      simpa [Prod.norm_def] using hh
    exact ht.trans (mul_le_mul_of_nonneg_right hM₂' (norm_nonneg _))
  · intro t d hp
    have hp0 : (t, (0 : ℂ)) ∈ Metric.ball (0, 0) r := by
      have ht : ‖t‖ < r := (le_max_left ‖t‖ ‖d‖).trans_lt
        (by simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using hp)
      simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using ht
    have hh := (convex_ball (0 : ℂ × ℂ) r₃).norm_image_sub_le_of_norm_fderiv_le
      (fun p hp' => (ha₃ p hp').differentiableAt) hb₃
      (Metric.ball_subset_ball h₃ hp0) (Metric.ball_subset_ball h₃ hp)
    have ht : ‖angularJet 3 g (t, d)‖ ≤ M₃ * ‖d‖ := by
      simpa [angularJet_three_zero heven t, Prod.norm_def] using hh
    exact ht.trans (mul_le_mul_of_nonneg_right hM₃' (norm_nonneg _))

end
end IsingBulk.AnisoF002.NegativeHT
