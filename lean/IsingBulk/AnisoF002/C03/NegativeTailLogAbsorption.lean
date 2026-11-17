import IsingBulk.AnisoF002.C03.NegativeCentralScaling

/-!
# Direct uniform logarithmic absorption on the outer real radial region

A smaller fixed pole ball gives a uniform small multiple of log(1+x)
for the complete pole error.  The full density logarithm then costs
O(1/n) of the Taylor-order radial decay.  This supplies the tail step
without deleting any angular directions or altering the physical density.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem div_one_add_le_log {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hp : 0 < 1 + x := by linarith
  calc
    _ = 1 - (1 + x)⁻¹ := by field_simp; ring
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos hp

set_option maxHeartbeats 1000000 in
theorem radial_density_log_ratio {N k x : ℝ}
    (hN : 1 ≤ N) (hk : N ^ 2 ≤ k) (hx : 0 < x)
    (hxlow : N ^ 2 ≤ k * x) (hxhigh : x ≤ N) :
    Real.sqrt x + x ≤ 4 * k / N * Real.log (1 + x) := by
  have hN0 : 0 < N := by linarith
  have hk0 : 0 < k := (sq_pos_of_pos hN0).trans_le hk
  have hu := Real.sqrt_pos.mpr hx
  have husq := Real.sq_sqrt hx.le
  have hku : N ^ 2 ≤ k * Real.sqrt x := by
    by_cases hu1 : 1 ≤ Real.sqrt x
    · exact hk.trans (le_mul_of_one_le_right hk0.le hu1)
    · have hu1' : Real.sqrt x ≤ 1 := le_of_not_ge hu1
      have hxu : x ≤ Real.sqrt x := by nlinarith
      exact hxlow.trans (mul_le_mul_of_nonneg_left hxu hk0.le)
  have hroot : Real.sqrt x ≤ k * x / N ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN0)).mpr
    have hh := mul_le_mul_of_nonneg_right hku hu.le
    nlinarith [husq]
  have hx' : x ≤ k * x / N ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN0)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hk hx.le]
  have hsum : Real.sqrt x + x ≤ 2 * k * x / N ^ 2 := by
    calc
      _ ≤ k * x / N ^ 2 + k * x / N ^ 2 := add_le_add hroot hx'
      _ = _ := by ring
  have hhigh : 1 + x ≤ 2 * N := by linarith
  have hr : (Real.sqrt x + x) * (1 + x) ≤ 4 * k * x / N := by
    calc
      _ ≤ (2 * k * x / N ^ 2) * (2 * N) :=
        mul_le_mul hsum hhigh (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hratio : Real.sqrt x + x ≤ (4 * k / N) * (x / (1 + x)) := by
    calc
      _ ≤ (4 * k * x / N) / (1 + x) := (le_div_iff₀ (by positivity)).mpr hr
      _ = _ := by ring
  exact hratio.trans (mul_le_mul_of_nonneg_left (div_one_add_le_log hx.le) (by positivity))

theorem density_log_absorption {N k x L E : ℝ}
    (hN : 1 ≤ N) (hk : N ^ 2 ≤ k) (hx : 0 < x)
    (hxlow : N ^ 2 ≤ k * x) (hxhigh : x ≤ N) (hL : 0 ≤ L)
    (hlarge : 64 * L ≤ N) (hE : E ≤ L * (Real.sqrt x + x)) :
    E ≤ k / 16 * Real.log (1 + x) := by
  have hN0 : 0 < N := by linarith
  have hk0 : 0 ≤ k := (sq_nonneg N).trans hk
  have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hcoeff : 4 * L / N ≤ 1 / 16 := by
    apply (div_le_iff₀ hN0).mpr
    linarith
  calc
    _ ≤ L * (Real.sqrt x + x) := hE
    _ ≤ L * (4 * k / N * Real.log (1 + x)) :=
      mul_le_mul_of_nonneg_left (radial_density_log_ratio hN hk hx hxlow hxhigh) hL
    _ = (4 * L / N) * k * Real.log (1 + x) := by ring
    _ ≤ (1 / 16 : ℝ) * k * Real.log (1 + x) := by gcongr
    _ = _ := by ring

theorem small_pole_log_absorption {N k Q a τ x R : ℝ}
    (hN : 0 < N) (hk : 0 ≤ k) (hQ : 0 ≤ Q) (ha : (1 / 2 : ℝ) ≤ a)
    (hτ : 0 < τ) (hx : 0 ≤ x) (hscale : τ * x = a * Q / (2 * N))
    (hR : R ≤ Q / (256 * N)) :
    2 * k * R / (τ + a * Q / (2 * N)) ≤ k / 32 * Real.log (1 + x) := by
  have hD : 0 < τ + a * Q / (2 * N) := by positivity
  have hR' : R ≤ τ * x / 64 := by
    rw [hscale]
    apply hR.trans
    have hh := mul_le_mul_of_nonneg_right ha (div_nonneg hQ hN.le)
    have he : Q / (256 * N) ≤ (a * Q / (2 * N)) / 64 := by
      convert (mul_le_mul_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 1 / 128)) using 1 <;> ring
    exact he
  have hde : τ + a * Q / (2 * N) = τ * (1 + x) := by rw [← hscale]; ring
  calc
    _ ≤ 2 * k * (τ * x / 64) / (τ + a * Q / (2 * N)) := by gcongr
    _ = (k / 32) * (x / (1 + x)) := by rw [hde]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_one_add_le_log hx) (by positivity)

theorem full_tail_log_absorption {N k Q a τ x R L E : ℝ}
    (hN : 1 ≤ N) (hk : N ^ 2 ≤ k) (hQ : 0 ≤ Q) (ha : (1 / 2 : ℝ) ≤ a)
    (hτ : 0 < τ) (hx : 0 < x) (hscale : τ * x = a * Q / (2 * N))
    (hxlow : N ^ 2 ≤ k * x) (hxhigh : x ≤ N) (hL : 0 ≤ L)
    (hlarge : 64 * L ≤ N) (hE : E ≤ L * (Real.sqrt x + x))
    (hR : R ≤ Q / (256 * N)) :
    E + 2 * k * R / (τ + a * Q / (2 * N)) ≤ k / 8 * Real.log (1 + x) := by
  have hN0 : 0 < N := by linarith
  have hk0 : 0 ≤ k := (sq_nonneg N).trans hk
  have hd := density_log_absorption hN hk hx hxlow hxhigh hL hlarge hE
  have hp := small_pole_log_absorption hN0 hk0 hQ ha hτ hx.le hscale hR
  have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  nlinarith [mul_nonneg hk0 hlog]

end
end IsingBulk.AnisoF002.NegativeHT
