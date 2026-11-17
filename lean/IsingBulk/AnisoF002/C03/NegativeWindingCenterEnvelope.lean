import IsingBulk.AnisoF002.C03.RegularWindingNumeratorBound
import IsingBulk.AnisoF002.C03.NegativeHighParticleMass

/-!
# Exact center normalization and the all-order high-particle scale

The physical center factor has at most exponential N² growth.  Combining
it with the complete Vandermonde mass preserves the negative leading
half N² log N term, with no relation between N and the Taylor order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

theorem allWindingCenterMagnitude_le_power (n : ℕ) (b0 : ℂ) {φ : ℝ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) :
    allWindingCenterMagnitude n b0 φ ≤ (‖b0‖ / Real.sin φ) ^ (n ^ 2) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hπ2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.one_le_pi_div_two]
  have htwopi : (1 : ℝ) ≤ (2 * Real.pi) ^ (n - 1) := one_le_pow₀ hπ2
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (n * (n - 1)) := one_le_pow₀ (by norm_num)
  have hprod : (1 : ℝ) ≤ (n.factorial : ℝ) * (2 * Real.pi) ^ (n - 1) * (2 : ℝ) ^ (n * (n - 1)) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf htwopi) htwo
  unfold allWindingCenterMagnitude
  rw [div_pow]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg b0) _) (pow_pos hs _)
    (by nlinarith [pow_pos hs (n ^ 2)])

theorem exists_allWindingCenterMagnitude_exponential (b0 : ℂ) {φ : ℝ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ n : ℕ,
      allWindingCenterMagnitude n b0 φ ≤ Real.exp (C0 * (n : ℝ) ^ 2) := by
  let x := ‖b0‖ / Real.sin φ
  have hx : 0 ≤ x := div_nonneg (norm_nonneg _) (Real.sin_pos_of_pos_of_lt_pi hφ hπ).le
  have hC : 0 < x + 1 := by linarith
  refine ⟨x + 1, hC, ?_⟩
  intro n
  have hxexp : x ≤ Real.exp (x + 1) := by linarith [Real.add_one_le_exp (x + 1)]
  apply (allWindingCenterMagnitude_le_power n b0 hφ hπ).trans
  calc
    x ^ (n ^ 2) ≤ (Real.exp (x + 1)) ^ (n ^ 2) := pow_le_pow_left₀ hx hxexp _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem high_particle_scalar_envelope {A C C0 lambda σ : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (hlambda : 0 < lambda)
    (hσ : σ ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ N j : ℕ, 1 ≤ N →
      (2 * (N : ℝ) + 1) *
        (2 * Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) * σ) / (A * (N : ℝ))) *
        ((N : ℝ) ^ 2 / lambda) ^ (j + 1) *
        Real.exp (-(N : ℝ) ^ 2 / 2 * Real.log (N : ℝ) + 4 * (N : ℝ) ^ 2) ≤
      Real.exp (2 * (j : ℝ) * Real.log (N : ℝ) - (N : ℝ) ^ 2 / 2 * Real.log (N : ℝ) +
        D * (N : ℝ) ^ 2 + D * (j : ℝ) + D) := by
  let D := C0 + C + 6 + |Real.log lambda| + |Real.log (6 / A)|
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro N j hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hcount : (2 * (N : ℝ) + 1) / (N : ℝ) ≤ 3 := by
    apply (div_le_iff₀ hN0).mpr
    linarith
  have hmain : (2 * (N : ℝ) + 1) *
      (2 * Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) * σ) / (A * (N : ℝ))) ≤
        (6 / A) * Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) ^ 2) := by
    calc
      _ = ((2 * (N : ℝ) + 1) / (N : ℝ)) * (2 / A) *
          Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) * σ) := by ring
      _ ≤ 3 * (2 / A) * Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) ^ 2) := by
        have hleft : ((2 * (N : ℝ) + 1) / (N : ℝ)) * (2 / A) * Real.exp (C0 * (N : ℝ) ^ 2) ≤
            3 * (2 / A) * Real.exp (C0 * (N : ℝ) ^ 2) := by gcongr
        have hexp : Real.exp (C * (N : ℝ) * σ) ≤ Real.exp (C * (N : ℝ) ^ 2) := by
          apply Real.exp_le_exp.mpr
          calc
            _ ≤ C * (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hσ (mul_nonneg hC hN0.le)
            _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hNsq hC
        exact mul_le_mul hleft hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hpos : 0 < (N : ℝ) ^ 2 / lambda := by positivity
  have hpower : ((N : ℝ) ^ 2 / lambda) ^ (j + 1) =
      Real.exp (((j + 1 : ℕ) : ℝ) * (2 * Real.log (N : ℝ) - Real.log lambda)) := by
    have hlog : Real.log ((N : ℝ) ^ 2 / lambda) = 2 * Real.log (N : ℝ) - Real.log lambda := by
      rw [Real.log_div (by positivity) hlambda.ne', Real.log_pow]
      norm_num
    rw [← hlog, Real.exp_nat_mul, Real.exp_log hpos]
  have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) ^ 2 :=
    (Real.log_le_sub_one_of_pos hN0).trans (by nlinarith)
  calc
    _ ≤ ((6 / A) * Real.exp (C0 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) ^ 2)) *
        ((N : ℝ) ^ 2 / lambda) ^ (j + 1) *
        Real.exp (-(N : ℝ) ^ 2 / 2 * Real.log (N : ℝ) + 4 * (N : ℝ) ^ 2) := by gcongr
    _ = Real.exp (Real.log (6 / A) + C0 * (N : ℝ) ^ 2 + C * (N : ℝ) ^ 2 +
        ((j + 1 : ℕ) : ℝ) * (2 * Real.log (N : ℝ) - Real.log lambda) +
        (-(N : ℝ) ^ 2 / 2 * Real.log (N : ℝ) + 4 * (N : ℝ) ^ 2)) := by
      rw [hpower]
      conv_rhs =>
        rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log (by positivity : 0 < 6 / A)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hlam := neg_le_abs (Real.log lambda)
      have hconst := le_abs_self (Real.log (6 / A))
      have hj := Nat.cast_nonneg (α := ℝ) j
      dsimp [D]
      push_cast
      nlinarith [abs_nonneg (Real.log lambda), abs_nonneg (Real.log (6 / A)),
        sq_nonneg (N : ℝ)])

end
end IsingBulk.AnisoF002.NegativeHT
