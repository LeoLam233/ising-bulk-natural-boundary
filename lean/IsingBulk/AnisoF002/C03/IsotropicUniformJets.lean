import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
# Dimension-independent fixed joint jets on protected complex balls

This generic analytic estimate supplies all fixed Fréchet jets from one
complex neighborhood bound. It is used for the actual complete F002
products, so its constants do not grow with the number of coordinates.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

noncomputable def protectedJetConstant : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, r => 4 * protectedJetConstant k (r / 2) / r

theorem protectedJetConstant_pos (k : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < protectedJetConstant k r := by
  induction k generalizing r with
  | zero => exact zero_lt_one
  | succ k ih =>
    exact div_pos (mul_pos (by norm_num) (ih (half_pos hr))) hr

theorem analytic_ball_joint_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (k : ℕ) (f : E → F) (x : E) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball x r))
    (hbound : ∀ y ∈ ball x r, ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ protectedJetConstant k r * M := by
  induction k generalizing x r with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, protectedJetConstant, one_mul] using
      hbound x (mem_ball_self hr)
  | succ k ih =>
    have hhalf : 0 < r / 2 := half_pos hr
    have hsub : ∀ y ∈ ball x (r / 2), ball y (r / 2) ⊆ ball x r := by
      intro y hy z hz
      rw [mem_ball] at hy hz ⊢
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ < r := by linarith
    have hjet : ∀ y ∈ ball x (r / 2),
        ‖iteratedFDeriv ℂ k f y‖ ≤ protectedJetConstant k (r / 2) * M := by
      intro y hy
      exact ih y (r / 2) hhalf (hf.mono (hsub y hy))
        (fun z hz => hbound z (hsub y hy hz))
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ k f) (ball x (r / 2)) :=
      ((hf.mono (ball_subset_ball (by linarith : r / 2 ≤ r))).iteratedFDeriv k).differentiableOn
    have hmaps : MapsTo (iteratedFDeriv ℂ k f) (ball x (r / 2))
        (closedBall (iteratedFDeriv ℂ k f x) (2 * (protectedJetConstant k (r / 2) * M))) := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hjet y hy, hjet x (mem_ball_self hhalf)])
    have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hdiff hmaps hhalf
    rw [norm_fderiv_iteratedFDeriv] at h
    have he : (2 * (protectedJetConstant k (r / 2) * M)) / (r / 2) =
        protectedJetConstant (k + 1) r * M := by
      simp only [protectedJetConstant]
      ring
    exact h.trans_eq he

end IsingBulk.AnisoF002.Isotropic
