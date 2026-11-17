import IsingBulk.AnisoF002.C03.IsotropicCollisionScale

/-!
# Continuous zero values for retained collision currents

Only a value on the full-coincidence set is filled. The estimate uses
the actual retained power, and every off-coincidence value and
derivative remains unchanged.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology Classical

variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F]

def zeroAtCoincidence (f : E → F) (x : E) : F := if x = 0 then 0 else f x

theorem zeroAtCoincidence_zero (f : E → F) : zeroAtCoincidence f 0 = 0 := by
  simp only [zeroAtCoincidence, ite_true]

theorem zeroAtCoincidence_germ {f : E → F} {x : E} (hx : x ≠ 0) :
    zeroAtCoincidence f =ᶠ[𝓝 x] f := by
  filter_upwards [continuousAt_id.eventually_ne hx] with y hy
  change y ≠ 0 at hy
  simp only [zeroAtCoincidence, hy, ite_false]

theorem zeroAtCoincidence_continuousAt_zero (f : E → F) (C r : ℝ) (p : ℕ)
    (hC : 0 ≤ C) (hr : 0 < r) (hp : 1 ≤ p)
    (hbound : ∀ x ∈ ball (0 : E) r, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ p) :
    ContinuousAt (zeroAtCoincidence f) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ := min r (min 1 (ε / (C + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [zeroAtCoincidence_zero, dist_zero_right]
  by_cases hx0 : x = 0
  · subst x
    simpa only [zeroAtCoincidence_zero, norm_zero] using hε
  have hxnorm : ‖x‖ < δ := by simpa only [dist_zero_right] using hx
  have hxr : x ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right]
    exact hxnorm.trans_le (min_le_left _ _)
  have hx1 : ‖x‖ ≤ 1 := (hxnorm.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hxε : ‖x‖ < ε / (C + 1) := hxnorm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpw : ‖x‖ ^ p ≤ ‖x‖ := by
    simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg x) hx1 hp
  rw [zeroAtCoincidence, ite_eq_right hx0]
  calc
    ‖f x‖ ≤ C * ‖x‖ ^ p := hbound x hxr hx0
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_left hpw hC
    _ ≤ (C + 1) * ‖x‖ := by nlinarith only [norm_nonneg x]
    _ < ε := by
      have hh := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hxε
      simpa only [mul_comm] using hh

theorem zeroAtCoincidence_continuous (f : E → F) (C r : ℝ) (p : ℕ)
    (hC : 0 ≤ C) (hr : 0 < r) (hp : 1 ≤ p)
    (hreg : ∀ x : E, x ≠ 0 → ContinuousAt f x)
    (hbound : ∀ x ∈ ball (0 : E) r, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ p) :
    Continuous (zeroAtCoincidence f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact zeroAtCoincidence_continuousAt_zero f C r p hC hr hp hbound
  · exact (hreg x hx).congr (zeroAtCoincidence_germ hx).symm

theorem retained_power_division {Δ : ℝ} (hΔ : Δ ≠ 0) {d e : ℕ} (hed : e ≤ d) :
    Δ ^ d / Δ ^ e = Δ ^ (d - e) := (pow_sub₀ Δ hΔ hed).symm

theorem retained_power_vanishing_bound {Δ L u : ℝ} {d e : ℕ}
    (hΔ : 0 < Δ) (hΔu : Δ ≤ L * u) (hed : e ≤ d) :
    Δ ^ d / Δ ^ e ≤ L ^ (d - e) * u ^ (d - e) := by
  rw [retained_power_division hΔ.ne' hed, ← mul_pow]
  exact pow_le_pow_left₀ hΔ.le hΔu _

theorem retained_power_uniform_bound {Δ D : ℝ} {d e : ℕ}
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D) (hed : e ≤ d) :
    Δ ^ d / Δ ^ e ≤ (max 1 D) ^ d := by
  rw [retained_power_division hΔ.ne' hed]
  exact (pow_le_pow_left₀ hΔ.le (hΔD.trans (le_max_right _ _)) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))

end
end IsingBulk.AnisoF002.Isotropic
