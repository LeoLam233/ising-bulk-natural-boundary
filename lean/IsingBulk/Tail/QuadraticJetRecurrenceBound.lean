import Mathlib.Tactic

/-! Explicit finite-order polynomial bound for an exact inverse-jet recurrence. -/
namespace IsingBulk.Tail
noncomputable section

theorem quadratic_jet_recurrence_one_le (R : ℕ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (h0 : R 0=1) (hstep : ∀ j : ℕ, R (j+1)=R j+(4:ℝ)^j*(R j)^2*B) :
    ∀ j : ℕ, 1 ≤ R j := by
  intro j
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    rw [hstep]
    have hp : 0 ≤ (4:ℝ)^j*(R j)^2*B := by positivity
    linarith

theorem quadratic_jet_recurrence_bound (R : ℕ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (h0 : R 0=1) (hstep : ∀ j : ℕ, R (j+1)=R j+(4:ℝ)^j*(R j)^2*B)
    (J : ℕ) : ∀ j : ℕ, j ≤ J → R j ≤ (2*(4:ℝ)^J*B)^(2^j-1) := by
  have hR := quadratic_jet_recurrence_one_le R hB h0 hstep
  have hS : 1 ≤ (4:ℝ)^J*B := by
    have hp : (1:ℝ) ≤ 4^J := one_le_pow₀ (by norm_num)
    nlinarith
  have hK : 0 ≤ 2*(4:ℝ)^J*B := by positivity
  intro j
  induction j with
  | zero => intro _; simp [h0]
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hcoeff : (4:ℝ)^j ≤ 4^J := pow_le_pow_right₀ (by norm_num) (by omega)
    have hRsq : R j ≤ (R j)^2 := by nlinarith [hR j]
    have hcoeff' : (4:ℝ)^j*B ≤ (4:ℝ)^J*B := mul_le_mul_of_nonneg_right hcoeff (by linarith)
    have hstepbound : R (j+1) ≤ (2*(4:ℝ)^J*B)*(R j)^2 := by
      rw [hstep]
      have hh := mul_le_mul_of_nonneg_right hcoeff' (sq_nonneg (R j))
      have hh2 := mul_le_mul_of_nonneg_right hS (sq_nonneg (R j))
      nlinarith
    calc
      R (j+1) ≤ (2*(4:ℝ)^J*B)*(R j)^2 := hstepbound
      _ ≤ (2*(4:ℝ)^J*B)*((2*(4:ℝ)^J*B)^(2^j-1))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hR j]) hprev 2) hK
      _ = (2*(4:ℝ)^J*B)^(2^(j+1)-1) := by
        rw [← pow_mul,← pow_succ']
        congr 1
        rw [pow_succ]
        have hp : 1 ≤ (2:ℕ)^j := Nat.one_le_pow j 2 (by omega)
        omega

end
end IsingBulk.Tail
