import IsingBulk.AnisoF002.C03.RegularCompactIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Compact analytic integrals and normally convergent analytic series

These generic tools identify actual derivatives of integrals and infinite
sums.  The summable derivative bounds are obtained by Cauchy on one common
disk from a bound on the actual functions.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem analyticAt_integral_of_joint_analytic
    {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℂ × E → ℂ} {g : X → E} {K : Set X} {t : ℂ}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hg : Continuous g)
    (hf : ∀ x ∈ K, AnalyticAt ℂ f (t, g x)) :
    AnalyticAt ℂ (fun u : ℂ => ∫ x, f (u, g x) ∂μ) t := by
  obtain ⟨r, hr, hnear⟩ := joint_analytic_compact_parameter_disk hK hg hf
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Metric.closedBall_mem_nhds t hr] with u hu
  exact (integral_hasDerivAt_of_joint_analytic hK hμ hg (hnear u hu)).2.differentiableAt

theorem common_disk_iteratedDeriv_bound {f : ℂ → ℂ} {t x : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.closedBall t r))
    (hb : ∀ u ∈ Metric.closedBall t r, ‖f u‖ ≤ M)
    (hx : x ∈ Metric.closedBall t (r / 2)) (j : ℕ) :
    ‖iteratedDeriv j f x‖ ≤ (j.factorial : ℝ) * M / (r / 2) ^ j := by
  have hsub : Metric.closedBall x (r / 2) ⊆ Metric.closedBall t r := by
    apply Metric.closedBall_subset_closedBall'
    have h := Metric.mem_closedBall.mp hx
    linarith
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos hr)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (half_pos hr).ne']
    exact fun u hu => (hf u (hsub hu)).differentiableAt.differentiableWithinAt
  · exact fun u hu => hb u (hsub (Metric.sphere_subset_closedBall hu))

theorem hasDerivAt_tsum_jets_of_common_disk {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    {t x : ℂ} {r : ℝ} (hr : 0 < r) (hM : Summable M)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (Metric.closedBall t r))
    (hb : ∀ n u, u ∈ Metric.closedBall t r → ‖f n u‖ ≤ M n)
    (hx : x ∈ Metric.ball t (r / 2)) (j : ℕ) :
    HasDerivAt (fun u => ∑' n, iteratedDeriv j (f n) u)
      (∑' n, iteratedDeriv (j + 1) (f n) x) x := by
  let B (k : ℕ) (n : ℕ) : ℝ := (k.factorial : ℝ) * M n / (r / 2) ^ k
  have hBs (k : ℕ) : Summable (B k) := by
    convert hM.mul_left ((k.factorial : ℝ) / (r / 2) ^ k) using 1
    funext n
    dsimp [B]
    ring
  have hjet (k : ℕ) (n : ℕ) (u : ℂ) (hu : u ∈ Metric.ball t (r / 2)) :
      ‖iteratedDeriv k (f n) u‖ ≤ B k n :=
    common_disk_iteratedDeriv_bound hr (hf n) (hb n) (Metric.ball_subset_closedBall hu) k
  apply hasDerivAt_tsum_of_isPreconnected (hBs (j + 1)) Metric.isOpen_ball
    (convex_ball t (r / 2)).isPreconnected
    (g := fun n => iteratedDeriv j (f n)) (g' := fun n => iteratedDeriv (j + 1) (f n))
    (y₀ := t)
  · intro n u hu
    have ha := (hf n u (Metric.closedBall_subset_closedBall (half_le_self hr.le)
      (Metric.ball_subset_closedBall hu))).iterated_deriv j
    simpa only [iteratedDeriv_succ, iteratedDeriv_eq_iterate] using ha.differentiableAt.hasDerivAt
  · exact hjet (j + 1)
  · exact Metric.mem_ball_self (half_pos hr)
  · exact (hBs j).of_norm_bounded fun n => hjet j n t (Metric.mem_ball_self (half_pos hr))
  · exact hx

/-- Repeated derivatives of the actual infinite sum agree with the
series of actual term derivatives throughout a common smaller disk. -/
theorem iteratedDeriv_tsum_of_common_disk {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    {t x : ℂ} {r : ℝ} (hr : 0 < r) (hM : Summable M)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (Metric.closedBall t r))
    (hb : ∀ n u, u ∈ Metric.closedBall t r → ‖f n u‖ ≤ M n)
    (hx : x ∈ Metric.ball t (r / 2)) (j : ℕ) :
    iteratedDeriv j (fun u => ∑' n, f n u) x = ∑' n, iteratedDeriv j (f n) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have heq : (fun u => iteratedDeriv j (fun v => ∑' n, f n v) u) =ᶠ[𝓝 x]
        fun u => ∑' n, iteratedDeriv j (f n) u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with u hu
      exact ih hu
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (hasDerivAt_tsum_jets_of_common_disk hr hM hf hb hx j).deriv

theorem analyticAt_tsum_of_common_disk {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    {t : ℂ} {r : ℝ} (hr : 0 < r) (hM : Summable M)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (Metric.closedBall t r))
    (hb : ∀ n u, u ∈ Metric.closedBall t r → ‖f n u‖ ≤ M n) :
    AnalyticAt ℂ (fun u => ∑' n, f n u) t := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Metric.ball_mem_nhds t (half_pos hr)] with u hu
  exact (hasDerivAt_tsum_jets_of_common_disk hr hM hf hb hu 0).differentiableAt

end
end IsingBulk.AnisoF002.RegularTail.C03
