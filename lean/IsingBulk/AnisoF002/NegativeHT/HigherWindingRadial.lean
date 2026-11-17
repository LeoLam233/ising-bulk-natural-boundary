import IsingBulk.AnisoF002.NegativeHT.RadialBetaTail
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Complete higher-winding sum of the real-cycle radial periods

F002 `eq:jets_beta_integral` gives an exact winding dependence
`|w|^(-2*(j+1-α))`; `eq:jets_higher_windings_negligible` then sums every
higher odd winding.  This file proves that dependence for the actual
complex radial integrals and sums the full infinite scalar majorant.
The physical residue and numerator bounds remain separate obligations.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The positive and negative higher odd winding indices are all covered. -/
theorem higherOddWinding_parameterization {w : ℤ} (hw : Odd w) (hm : 3≤|w|) :
    ∃ r : ℕ, w=2*(r:ℤ)+3 ∨ w=-(2*(r:ℤ)+3) := by
  obtain ⟨a, ha⟩ := hw
  rcases le_or_gt 0 w with hp | hn
  · rw [abs_of_nonneg hp] at hm
    have hr : 0≤a-1 := by omega
    refine ⟨(a-1).toNat, Or.inl ?_⟩
    rw [Int.toNat_of_nonneg hr]
    omega
  · rw [abs_of_neg hn] at hm
    have hr : 0≤-a-2 := by omega
    refine ⟨(-a-2).toNat, Or.inr ?_⟩
    rw [Int.toNat_of_nonneg hr]
    omega

/-- A telescoping comparison gives a fixed bound for the entire inverse
square series; no cutoff is present in the final winding estimate. -/
theorem sum_range_inverse_square_le (N : ℕ) :
    ∑ r ∈ Finset.range N, 1/((r:ℝ)+1)^2 ≤ 2-2/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hN : (0:ℝ)<(N:ℝ)+1 := by positivity
    have hN2 : (0:ℝ)<(N:ℝ)+2 := by positivity
    have hp : 1/((N:ℝ)+1)^2 ≤ 2/((N:ℝ)+1)-2/((N:ℝ)+2) := by
      rw [show 2/((N:ℝ)+1)-2/((N:ℝ)+2) =
          2/(((N:ℝ)+1)*((N:ℝ)+2)) by field_simp; ring]
      apply (div_le_div_iff₀ (sq_pos_of_pos hN) (mul_pos hN hN2)).mpr
      nlinarith
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (N:ℝ)+1+1 = (N:ℝ)+2 by ring]
    linarith

/-- A uniform pointwise comparison of all higher odd winding powers. -/
theorem higherOddWinding_power_le (p r : ℕ) (hp : 2≤p) :
    1/(2*(r:ℝ)+3)^p ≤ (9/(3:ℝ)^p)*(1/((r:ℝ)+1)^2) := by
  have hx : (0:ℝ)<2*(r:ℝ)+3 := by positivity
  have hy : (0:ℝ)<(r:ℝ)+1 := by positivity
  have hrat : 3/(2*(r:ℝ)+3)≤1 := (div_le_one hx).mpr
    (by linarith [show (0:ℝ)≤r by positivity])
  have hpow := pow_le_pow_of_le_one (by positivity : (0:ℝ)≤3/(2*(r:ℝ)+3)) hrat hp
  have he : 1/(2*(r:ℝ)+3)^p ≤ (9/(3:ℝ)^p)*(1/(2*(r:ℝ)+3)^2) := by
    have hm := div_le_div_of_nonneg_right hpow (show (0:ℝ)≤(3:ℝ)^p by positivity)
    convert hm using 1 <;> rw [div_pow] <;> field_simp
    norm_num
  calc
    _ ≤ (9/(3:ℝ)^p)*(1/(2*(r:ℝ)+3)^2) := he
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hy)
      nlinarith

/-- Uniform bound on every finite initial set of higher positive windings. -/
theorem sum_range_higherOddWinding_le (p N : ℕ) (hp : 2≤p) :
    ∑ r ∈ Finset.range N, 1/(2*(r:ℝ)+3)^p ≤ 18/(3:ℝ)^p := by
  calc
    _ ≤ ∑ r ∈ Finset.range N, (9/(3:ℝ)^p)*(1/((r:ℝ)+1)^2) :=
      Finset.sum_le_sum (fun r _ => higherOddWinding_power_le p r hp)
    _ = (9/(3:ℝ)^p)*(∑ r ∈ Finset.range N, 1/((r:ℝ)+1)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (9/(3:ℝ)^p)*2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_range_inverse_square_le N).trans
        (by linarith [show (0:ℝ)≤2/((N:ℝ)+1) by positivity])
    _ = _ := by ring

/-- Summability is proved for the complete infinite winding majorant. -/
theorem summable_higherOddWinding_power (p : ℕ) (hp : 2≤p) :
    Summable (fun r : ℕ => 1/(2*(r:ℝ)+3)^p) := by
  exact summable_of_sum_range_le (fun _ => by positivity)
    (fun N => sum_range_higherOddWinding_le p N hp)

theorem tsum_higherOddWinding_power_le (p : ℕ) (hp : 2≤p) :
    (∑' r : ℕ, 1/(2*(r:ℝ)+3)^p) ≤ 18/(3:ℝ)^p := by
  exact Real.tsum_le_of_sum_range_le (fun _ => by positivity)
    (fun N => sum_range_higherOddWinding_le p N hp)

/-- The actual evaluated radial integral has exactly the winding power
asserted by the paper.  The complex curvature is retained. -/
theorem norm_radialPeriod_winding (α j : ℕ) {τ w : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hw : 0<w) (hh : 0<h.re) :
    ‖complexRadialPeriod α j (τ*w^2) h‖ =
      ‖complexRadialPeriod α j τ h‖ / w^(2*(j+1-α)) := by
  rw [norm_complexRadialPeriod α j hα hj (mul_pos hτ (sq_pos_of_pos hw)) hh,
    norm_complexRadialPeriod α j hα hj hτ hh]
  rw [mul_pow, ← pow_mul]
  simp only [mul_assoc, div_mul_eq_div_div]

/-- Every higher positive-winding radial period forms an absolutely
summable family, throughout the complete beta convergence range. -/
theorem summable_higherWinding_radialPeriod (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    Summable (fun r : ℕ => ‖complexRadialPeriod α j
      (τ*(2*(r:ℝ)+3)^2) h‖) := by
  have hp : 2≤2*(j+1-α) := by omega
  have hs := (summable_higherOddWinding_power (2*(j+1-α)) hp).mul_left
    ‖complexRadialPeriod α j τ h‖
  apply hs.congr
  intro r
  rw [norm_radialPeriod_winding α j hα hj hτ (by positivity) hh]
  ring

/-- The two signs of every higher odd winding together have a complete
integrated radial majorant, with exponential decay in Taylor order. -/
theorem higherWinding_radialPeriod_sum_le (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    2*(∑' r : ℕ, ‖complexRadialPeriod α j (τ*(2*(r:ℝ)+3)^2) h‖) ≤
      (36/(3:ℝ)^(2*(j+1-α)))*‖complexRadialPeriod α j τ h‖ := by
  have hp : 2≤2*(j+1-α) := by omega
  have he : (fun r : ℕ => ‖complexRadialPeriod α j (τ*(2*(r:ℝ)+3)^2) h‖) =
      (fun r : ℕ => ‖complexRadialPeriod α j τ h‖ * (1/(2*(r:ℝ)+3)^(2*(j+1-α)))) := by
    funext r
    rw [norm_radialPeriod_winding α j hα hj hτ (by positivity) hh]
    ring
  rw [he, tsum_mul_left]
  have hb := mul_le_mul_of_nonneg_left
    (tsum_higherOddWinding_power_le (2*(j+1-α)) hp)
    (norm_nonneg (complexRadialPeriod α j τ h))
  calc
    _ ≤ 2*(‖complexRadialPeriod α j τ h‖*(18/(3:ℝ)^(2*(j+1-α)))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end

end IsingBulk.AnisoF002.NegativeHT
