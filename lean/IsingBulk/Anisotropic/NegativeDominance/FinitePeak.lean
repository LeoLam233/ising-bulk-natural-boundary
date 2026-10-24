import IsingBulk.Anisotropic.NegativeDominance.DiscreteConcavity
import IsingBulk.Anisotropic.NegativeDominance.ExactModel

namespace IsingBulk.Anisotropic.NegativeDominance

theorem alpha_mono : Monotone alpha := by
  intro n m hnm
  unfold alpha
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.mul_self_le_mul_self hnm

/-- Concavity propagates a strict central gap through every index of an
arbitrary segment. The length is unrestricted and not fixed in advance. -/
theorem linear_decay_to (f : ℕ → ℝ) (a : ℝ) (k : ℕ)
    (h : ∀ m, m+2 ≤ k → f (m+2)-2*f (m+1)+f m ≤ 0)
    (hfirst : f 1-f 0 ≤ -a) : f k ≤ f 0-a*(k : ℝ) := by
  by_cases hk : k=0
  · subst k; simp
  have hq := quadratic_le_on_range f 0 (k-1)
    (fun m hm => by simpa using h m (by omega)) k (by omega)
  have hm := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ k by positivity)
  simp only [zero_mul] at hq
  nlinarith only [hq, hm]

end IsingBulk.Anisotropic.NegativeDominance
