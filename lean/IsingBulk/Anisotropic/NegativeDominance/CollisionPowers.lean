import IsingBulk.Anisotropic.NegativeDominance.OddIndices
import Mathlib.Data.Nat.Choose.Basic

/-! Exact odd-particle powers needed in the central density normalization. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem alpha_even (n : ℕ) (hn : Odd n) : Even (alpha n) := by
  obtain ⟨k, rfl⟩ := hn
  rw [alpha_two_mul_add_one]
  exact ⟨k * (k + 1), by ring⟩

theorem odd_two_mul_choose_two (n : ℕ) (hn : Odd n) :
    2 * n.choose 2 = n * (n - 1) := by
  obtain ⟨k, rfl⟩ := hn
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring]
  omega

theorem odd_collision_degree (n : ℕ) (hn : Odd n) :
    n + 2 * n.choose 2 = 2 * alpha n + 1 := by
  rw [odd_two_mul_choose_two n hn, two_mul_alpha_add_one n hn]
  obtain ⟨k, rfl⟩ := hn
  simp only [Nat.add_sub_cancel]
  ring

theorem imaginary_collision_power (s : ℂ) (n : ℕ) (hn : Odd n) :
    (s * Complex.I) ^ (2 * alpha n) = s ^ (2 * alpha n) := by
  rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
  obtain ⟨k, hk⟩ := alpha_even n hn
  rw [hk, pow_add]
  have hh : (-1 : ℂ)^k * (-1)^k = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [hh, mul_one]

end
end IsingBulk.Anisotropic.NegativeDominance
