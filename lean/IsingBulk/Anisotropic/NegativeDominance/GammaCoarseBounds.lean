import IsingBulk.Anisotropic.NegativeDominance.GrowingGammaDifferences

/-! A dimension-uniform coarse bound sufficient for strict concavity. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem gamma_alpha_error_le_step_square (n p j : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (hj : 2 * alpha (n + 4 * p) ≤ j) :
    (((2 * p * n + 2 * p^2 : ℕ) : ℝ)^2 + ((2 * p)^2 : ℕ) * (alpha (n + 4 * p) : ℝ)) /
      ((j : ℝ) - alpha (n + 4 * p)) ≤ 4 * ((2 * p : ℕ) : ℝ)^2 := by
  have ho' : Odd (n + 4 * p) := by
    obtain ⟨k, rfl⟩ := ho
    exact ⟨k + 2 * p, by ring⟩
  have ha := two_mul_alpha_add_one (n + 4 * p) ho'
  have har : 2 * (alpha (n + 4 * p) : ℝ) + 1 = ((n + 4 * p : ℕ) : ℝ)^2 := by
    exact_mod_cast (ha.trans (pow_two _).symm)
  have hm : (3 : ℝ) ≤ ((n + 4 * p : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ n + 4 * p by omega)
  have hA : (1 : ℝ) ≤ alpha (n + 4 * p) := by nlinarith [sq_nonneg (((n + 4 * p : ℕ) : ℝ) - 3)]
  have hjr : 2 * (alpha (n + 4 * p) : ℝ) ≤ j := by exact_mod_cast hj
  have hb : ((2 * p * n + 2 * p^2 : ℕ) : ℝ) ≤ ((2 * p : ℕ) : ℝ) * ((n + 4 * p : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (p : ℝ)]
  have hb2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ ((2 * p * n + 2 * p^2 : ℕ) : ℝ) by positivity) hb 2
  have hm2 : ((n + 4 * p : ℕ) : ℝ)^2 ≤ 3 * (alpha (n + 4 * p) : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hm2 (sq_nonneg (((2 * p : ℕ) : ℝ)))
  have hrem := mul_nonneg (sq_nonneg (((2 * p : ℕ) : ℝ)))
    (sub_nonneg.mpr hjr)
  apply (div_le_iff₀ (show 0 < (j : ℝ) - alpha (n + 4 * p) by linarith)).mpr
  push_cast at hb2 hmul hrem ⊢
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
