import IsingBulk.AnisoF002.C03.NegativeHighParticleMass
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Complete high-particle summation

The high-particle exponent is decreasing beyond an explicit threshold.
Its entire discrete infinite tail is bounded by one geometric sum, with
no finite truncation or unstated tail summability hypothesis.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped BigOperators

def highParticleExponent (j : ℕ) (C x : ℝ) : ℝ :=
  (j : ℝ) * Real.log x - x * Real.log x / 4 + C * x

theorem highParticleExponent_decrease {j : ℕ} {C X x : ℝ}
    (hX : 0 < X) (hx : X ≤ x)
    (hdec : (j : ℝ) / X + C + 1 ≤ Real.log X / 4) :
    highParticleExponent j C x ≤ highParticleExponent j C X - (x - X) := by
  have hx0 : 0 < x := hX.trans_le hx
  have hlog : 0 ≤ Real.log x - Real.log X :=
    sub_nonneg.mpr (Real.log_le_log hX hx)
  have hincr : Real.log x - Real.log X ≤ (x - X) / X := by
    simpa only [add_sub_cancel] using (log_increment_bounds hX (sub_nonneg.mpr hx)).2
  have hj := mul_le_mul_of_nonneg_left hincr (Nat.cast_nonneg j)
  have hr : (j : ℝ) * ((x - X) / X) = ((j : ℝ) / X) * (x - X) := by ring
  rw [hr] at hj
  have hxlog := mul_nonneg hx0.le hlog
  have hc := mul_le_mul_of_nonneg_right hdec (sub_nonneg.mpr hx)
  unfold highParticleExponent
  nlinarith

theorem highParticleExponent_square_form (j : ℕ) (C n : ℝ) :
    highParticleExponent j C (n ^ 2) =
      2 * (j : ℝ) * Real.log n - n ^ 2 / 2 * Real.log n + C * n ^ 2 := by
  rw [highParticleExponent, Real.log_pow]
  ring

theorem highParticleExponent_tail_pointwise {j N : ℕ} {C X : ℝ}
    (hN : 1 ≤ N) (hX : 0 < X) (hstart : X ≤ (N : ℝ) ^ 2)
    (hdec : (j : ℝ) / X + C + 1 ≤ Real.log X / 4) (m : ℕ) :
    Real.exp (highParticleExponent j C (((N + m : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (highParticleExponent j C X) * Real.exp (-(m : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hgap : (m : ℝ) ≤ (((N + m : ℕ) : ℝ) ^ 2) - X := by
    push_cast
    nlinarith
  have hx : X ≤ (((N + m : ℕ) : ℝ) ^ 2) := by linarith
  have he := highParticleExponent_decrease hX hx hdec
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem complete_high_particle_tail_bound {j N : ℕ} {C X : ℝ}
    (hN : 1 ≤ N) (hX : 0 < X) (hstart : X ≤ (N : ℝ) ^ 2)
    (hdec : (j : ℝ) / X + C + 1 ≤ Real.log X / 4) :
    Summable (fun m : ℕ => Real.exp (highParticleExponent j C (((N + m : ℕ) : ℝ) ^ 2))) ∧
      (∑' m : ℕ, Real.exp (highParticleExponent j C (((N + m : ℕ) : ℝ) ^ 2))) ≤
        Real.exp (highParticleExponent j C X) * ∑' m : ℕ, Real.exp (-(m : ℝ)) := by
  have hs : Summable (fun m : ℕ => Real.exp (highParticleExponent j C X) *
      Real.exp (-(m : ℝ))) := Real.summable_exp_neg_nat.mul_left _
  have hcomp := highParticleExponent_tail_pointwise hN hX hstart hdec
  have ht := hs.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hcomp
  refine ⟨ht, ?_⟩
  rw [← tsum_mul_left]
  exact ht.tsum_le_tsum hcomp hs

end
end IsingBulk.AnisoF002.NegativeHT
