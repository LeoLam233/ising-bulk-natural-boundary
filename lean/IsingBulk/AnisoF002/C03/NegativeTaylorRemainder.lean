import IsingBulk.AnisoF002.C03.NegativeUniformDensityLog
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Uniform scalar Taylor remainder for the higher moving-pole error

The fourth-order remainder is proved on an arbitrary complex convex
neighborhood by repeated mean-value estimates.  The explicit factorial
coefficients are retained; no unspecified asymptotic expansion is used.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology

theorem scalar_power_bound_of_derivative {s : Set ℂ} (hs : Convex ℝ s)
    {f f' : ℂ → ℂ} {c : ℂ} {M : ℝ} {k : ℕ}
    (hc : c ∈ s) (hM : 0 ≤ M) (hfc : f c = 0)
    (hderiv : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ s, ‖f' y‖ ≤ M * ‖y - c‖ ^ k) :
    ∀ x ∈ s, ‖f x‖ ≤ M * ‖x - c‖ ^ (k + 1) := by
  intro x hx
  have hseg := hs.segment_subset hc hx
  have hb (y : ℂ) (hy : y ∈ segment ℝ c x) : ‖deriv f y‖ ≤ M * ‖x - c‖ ^ k := by
    rw [(hderiv y (hseg hy)).deriv]
    apply (hbound y (hseg hy)).trans
    gcongr
    exact norm_sub_le_of_mem_segment hy
  have hh := (convex_segment c x).norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hderiv y (hseg hy)).differentiableAt) hb
    (left_mem_segment ℝ c x) (right_mem_segment ℝ c x)
  simpa only [hfc, sub_zero, pow_succ, mul_assoc] using hh

set_option maxHeartbeats 1000000 in
theorem scalar_third_taylor_remainder {s : Set ℂ} (hs : Convex ℝ s)
    {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f s) (hc : c ∈ s) (hM : 0 ≤ M)
    (hfour : ∀ y ∈ s, ‖deriv (deriv (deriv (deriv f))) y‖ ≤ M) :
    ∀ x ∈ s,
      ‖f x - f c - deriv f c * (x - c) -
        (deriv (deriv f) c / 2) * (x - c) ^ 2 -
        (deriv (deriv (deriv f)) c / 6) * (x - c) ^ 3‖ ≤ M * ‖x - c‖ ^ 4 := by
  let R₃ : ℂ → ℂ := fun x => deriv (deriv (deriv f)) x - deriv (deriv (deriv f)) c
  let R₂ : ℂ → ℂ := fun x => deriv (deriv f) x - deriv (deriv f) c -
    deriv (deriv (deriv f)) c * (x - c)
  let R₁ : ℂ → ℂ := fun x => deriv f x - deriv f c - deriv (deriv f) c * (x - c) -
    (deriv (deriv (deriv f)) c / 2) * (x - c) ^ 2
  let R₀ : ℂ → ℂ := fun x => f x - f c - deriv f c * (x - c) -
    (deriv (deriv f) c / 2) * (x - c) ^ 2 -
    (deriv (deriv (deriv f)) c / 6) * (x - c) ^ 3
  have hR₃ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₃ (deriv (deriv (deriv (deriv f))) x) x :=
    (hf x hx).deriv.deriv.deriv.differentiableAt.hasDerivAt.sub_const _
  have hR₂ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₂ (R₃ x) x := by
    have hl : HasDerivAt (fun y : ℂ => deriv (deriv (deriv f)) c * (y - c))
        (deriv (deriv (deriv f)) c) x := by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_const_mul (deriv (deriv (deriv f)) c)).scomp x
          ((hasDerivAt_id' x).sub_const c)
    exact ((hf x hx).deriv.deriv.differentiableAt.hasDerivAt.sub_const _).sub hl
  have hR₁ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₁ (R₂ x) x := by
    have hl : HasDerivAt (fun y : ℂ => deriv (deriv f) c * (y - c)) (deriv (deriv f) c) x := by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_const_mul (deriv (deriv f) c)).scomp x ((hasDerivAt_id' x).sub_const c)
    have hq := (((hasDerivAt_id' x).sub_const c).pow 2).const_smul (deriv (deriv (deriv f)) c / 2)
    convert (((hf x hx).deriv.differentiableAt.hasDerivAt.sub_const _).sub hl).sub hq using 1
    dsimp [R₁, R₂]
    ring
  have hR₀ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₀ (R₁ x) x := by
    have hl : HasDerivAt (fun y : ℂ => deriv f c * (y - c)) (deriv f c) x := by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_const_mul (deriv f c)).scomp x ((hasDerivAt_id' x).sub_const c)
    have hq := (((hasDerivAt_id' x).sub_const c).pow 2).const_smul (deriv (deriv f) c / 2)
    have ht := (((hasDerivAt_id' x).sub_const c).pow 3).const_smul (deriv (deriv (deriv f)) c / 6)
    convert ((((hf x hx).differentiableAt.hasDerivAt.sub_const _).sub hl).sub hq).sub ht using 1
    dsimp [R₀, R₁]
    ring
  have hb₃ : ∀ x ∈ s, ‖R₃ x‖ ≤ M * ‖x - c‖ ^ 1 :=
    scalar_power_bound_of_derivative (k := 0) hs hc hM (by simp [R₃]) hR₃
      (fun x hx => by simpa only [pow_zero, mul_one] using hfour x hx)
  have hb₂ : ∀ x ∈ s, ‖R₂ x‖ ≤ M * ‖x - c‖ ^ 2 :=
    scalar_power_bound_of_derivative (k := 1) hs hc hM (by simp [R₂]) hR₂ hb₃
  have hb₁ : ∀ x ∈ s, ‖R₁ x‖ ≤ M * ‖x - c‖ ^ 3 :=
    scalar_power_bound_of_derivative (k := 2) hs hc hM (by simp [R₁]) hR₁ hb₂
  exact scalar_power_bound_of_derivative (k := 3) hs hc hM (by simp) hR₀ hb₁

end
end IsingBulk.AnisoF002.NegativeHT
