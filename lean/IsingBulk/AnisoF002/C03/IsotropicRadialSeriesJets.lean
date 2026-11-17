import IsingBulk.AnisoF002.C03.IsotropicRadialJetIdentification
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic

/-!
# Actual termwise radial derivatives identify every jet of an extension

Local summable bounds on the actual term derivatives justify genuine
differentiation of the complete series along a nondegenerate physical
path. Any analytic germ agreeing with that full series must have exactly
these summed complex jets. No holomorphy of a prescribed model sum is
assumed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem radial_tsum_jets_hasDerivAt (f : ℕ → ℂ → ℂ) (p p' : ℝ → ℂ)
    {U : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n : ℕ, ∀ t ∈ U, AnalyticAt ℂ (f n) (p t))
    (hp : ∀ t ∈ U, HasDerivAt p (p' t) t) (hpB : ∀ t ∈ U, ‖p' t‖ ≤ B)
    (j : ℕ) {x : ℝ}
    (hzero : Summable (fun n : ℕ => iteratedDeriv j (f n) (p x)))
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ U)
    {M : ℕ → ℝ} (hM : Summable M)
    (hb : ∀ n : ℕ, ∀ t ∈ ball x r, ‖iteratedDeriv (j + 1) (f n) (p t)‖ ≤ M n) :
    HasDerivAt (fun t => ∑' n : ℕ, iteratedDeriv j (f n) (p t))
      (p' x * ∑' n : ℕ, iteratedDeriv (j + 1) (f n) (p x)) x := by
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ ball x r) :
      HasDerivAt (fun u => iteratedDeriv j (f n) (p u))
        (p' t * iteratedDeriv (j + 1) (f n) (p t)) t := by
    have ha : AnalyticAt ℂ (iteratedDeriv j (f n)) (p t) := by
      simpa only [iteratedDeriv_eq_iterate] using (hf n t (hball ht)).iterated_deriv j
    simpa only [Function.comp_def, smul_eq_mul, iteratedDeriv_succ] using
      ha.differentiableAt.hasDerivAt.scomp t (hp t (hball ht))
  have hdB (n : ℕ) (t : ℝ) (ht : t ∈ ball x r) :
      ‖p' t * iteratedDeriv (j + 1) (f n) (p t)‖ ≤ B * M n := by
    rw [norm_mul]
    exact mul_le_mul (hpB t (hball ht)) (hb n t ht) (norm_nonneg _) hB
  have hs := hasDerivAt_tsum_of_isPreconnected (hM.mul_left B) isOpen_ball
    (convex_ball x r).isPreconnected hd hdB (mem_ball_self hr) hzero (mem_ball_self hr)
  simpa only [tsum_mul_left] using hs

theorem radial_tsum_identifies_extension_jets (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (p p' : ℝ → ℂ) (U : Set ℝ) (hU : IsOpen U) (J : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n : ℕ, ∀ t ∈ U, AnalyticAt ℂ (f n) (p t))
    (hF : ∀ t ∈ U, AnalyticAt ℂ F (p t))
    (hp : ∀ t ∈ U, HasDerivAt p (p' t) t)
    (hp' : ∀ t ∈ U, p' t ≠ 0) (hpB : ∀ t ∈ U, ‖p' t‖ ≤ B)
    (heq : ∀ t ∈ U, F (p t) = ∑' n : ℕ, f n (p t))
    (hlocal : ∀ j : ℕ, j ≤ J → ∀ x ∈ U,
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
        ∃ M : ℕ → ℝ, Summable M ∧
          ∀ n : ℕ, ∀ t ∈ ball x r, ‖iteratedDeriv j (f n) (p t)‖ ≤ M n) :
    ∀ j : ℕ, j ≤ J → ∀ t ∈ U,
      (∑' n : ℕ, iteratedDeriv j (f n) (p t)) = iteratedDeriv j F (p t) := by
  apply radial_current_identifies_iteratedDeriv F
    (fun j t => ∑' n : ℕ, iteratedDeriv j (f n) (p t)) p p' U hU J hF hp hp'
  · intro t ht
    simpa only [iteratedDeriv_zero] using (heq t ht).symm
  · intro j hj t ht
    obtain ⟨r₀, hr₀, _, M₀, hM₀, hb₀⟩ := hlocal j (by omega) t ht
    have hsum : Summable (fun n : ℕ => iteratedDeriv j (f n) (p t)) :=
      hM₀.of_norm_bounded (fun n => hb₀ n t (mem_ball_self hr₀))
    obtain ⟨r, hr, hball, M, hM, hb⟩ := hlocal (j + 1) (by omega) t ht
    exact radial_tsum_jets_hasDerivAt f p p' hB hf hp hpB j hsum hr hball hM hb

end
end IsingBulk.AnisoF002.Isotropic
