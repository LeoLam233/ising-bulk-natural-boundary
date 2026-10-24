import IsingBulk.Anisotropic.NegativeDominance.FinitePeak
import Mathlib.Algebra.Ring.Parity

namespace IsingBulk.Anisotropic.NegativeDominance

theorem lattice_linear_forward (f : ℕ → ℝ) (a : ℝ) (q N U t k : ℕ)
    (ht : Odd t) (hNt : N ≤ t) (hU : t+2*q*k ≤ U)
    (hc : ∀ m, N ≤ m → Odd m → m+4*q ≤ U → f (m+4*q)-2*f (m+2*q)+f m ≤ 0)
    (hf : f (t+2*q)-f t ≤ -a) :
    f (t+2*q*k) ≤ f t-a*(k : ℝ) := by
  have h := linear_decay_to (fun r => f (t+2*q*r)) a k
    (fun m hm => by
      have ho : Odd (t+2*q*m) := by obtain ⟨v, rfl⟩ := ht; exact ⟨v+q*m, by ring⟩
      have hlow : N ≤ t+2*q*m := by omega
      have hmul := Nat.mul_le_mul_left (2*q) hm
      have hhigh : t+2*q*m+4*q ≤ U := by nlinarith only [hmul, hU]
      have hh := hc (t+2*q*m) hlow ho hhigh
      have h1 : t+2*q*m+4*q = t+2*q*(m+2) := by ring
      have h2 : t+2*q*m+2*q = t+2*q*(m+1) := by ring
      simpa only [h1, h2] using hh)
    (by simpa using hf)
  simpa only [Nat.mul_zero, Nat.add_zero] using h

theorem lattice_linear_backward (f : ℕ → ℝ) (a : ℝ) (q N U t k : ℕ)
    (ht : Odd t) (hNk : N ≤ t-2*q*k) (hkt : 2*q*k ≤ t) (htU : t ≤ U)
    (hc : ∀ m, N ≤ m → Odd m → m+4*q ≤ U → f (m+4*q)-2*f (m+2*q)+f m ≤ 0)
    (hf : f (t-2*q)-f t ≤ -a) :
    f (t-2*q*k) ≤ f t-a*(k : ℝ) := by
  have h := linear_decay_to (fun r => f (t-2*q*r)) a k
    (fun m hm => by
      have hmul := Nat.mul_le_mul_left (2*q) hm
      have hmt : 2*q*(m+2) ≤ t := hmul.trans hkt
      have hlow : N ≤ t-2*q*(m+2) := hNk.trans (Nat.sub_le_sub_left hmul t)
      have ho : Odd (t-2*q*(m+2)) := Nat.Odd.sub_even hmt ht ⟨q*(m+2), by ring⟩
      have h1 : t-2*q*(m+2)+2*q = t-2*q*(m+1) := by
        simp only [Nat.mul_add, Nat.mul_one] at hmt ⊢
        omega
      have h2 : t-2*q*(m+2)+4*q = t-2*q*m := by
        simp only [Nat.mul_add] at hmt ⊢
        omega
      have hhigh : t-2*q*(m+2)+4*q ≤ U := by rw [h2]; omega
      have hh := hc (t-2*q*(m+2)) hlow ho hhigh
      rw [h1, h2] at hh
      linarith only [hh])
    (by simpa using hf)
  simpa only [Nat.mul_zero, Nat.sub_zero] using h

end IsingBulk.Anisotropic.NegativeDominance
