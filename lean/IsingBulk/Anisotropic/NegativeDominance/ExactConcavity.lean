import IsingBulk.Anisotropic.NegativeDominance.ModelErrorBounds
import IsingBulk.Anisotropic.NegativeDominance.TauConvexity
import IsingBulk.Anisotropic.NegativeDominance.GrowingGammaDifferences

/-! Exact-factor upper second difference. All n-dependent analytic errors
are retained in a separately proved uniform bound. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem model_log_second_difference_upper
    (B R H : ℕ → ℂ) (B0 : ℂ) (s C : ℝ) (n p j : ℕ)
    (hn : 4 ≤ n) (hnodd : Odd n) (hj : alpha (n + 4 * p) < j) (hs : s ≠ 0)
    (hgood : ∀ k ≥ n, Odd k → B k ≠ 0 ∧ R k ≠ 0 ∧ H k ≠ 0 ∧ (R k)^2 = B k)
    (herr : ∀ k ≥ n, Odd k → |modelAnalyticError B0 (B k) (H k) k| ≤ C) :
    Real.log ‖model (B (n + 4 * p)) (R (n + 4 * p)) (H (n + 4 * p)) s (n + 4 * p) j‖ -
      2 * Real.log ‖model (B (n + 2 * p)) (R (n + 2 * p)) (H (n + 2 * p)) s (n + 2 * p) j‖ +
      Real.log ‖model (B n) (R n) (H n) s n j‖ ≤
      -((2 * p : ℕ) : ℝ)^2 * Real.log j + ((2 * p : ℕ) : ℝ)^2 * modelQuadraticConstant B0 s +
        2 * ((2 * p : ℕ) : ℝ)^3 + 4 * C +
        (((2 * p * n + 2 * p^2 : ℕ) : ℝ)^2 + ((2 * p)^2 : ℕ) * (alpha (n + 4 * p) : ℝ)) /
          ((j : ℝ) - alpha (n + 4 * p)) := by
  have hodd (q : ℕ) : Odd (n + 2 * q) := by
    obtain ⟨k, rfl⟩ := hnodd
    exact ⟨k + q, by ring⟩
  have hodd1 := hodd p
  have hodd2 : Odd (n + 4 * p) := by convert hodd (2 * p) using 1; ring
  have hmid := alpha_even_step (n + 2 * p) p hodd1
  have hlow := alpha_even_step n p hnodd
  have hind : n + 2 * p + 2 * p = n + 4 * p := by ring
  rw [hind] at hmid
  have hj1 : alpha (n + 2 * p) < j := by omega
  have hj0 : alpha n < j := by omega
  have hdec (k : ℕ) (hk : n ≤ k) (ho : Odd k) (hkj : alpha k < j) :=
    log_norm_model_decomposition B0 (B k) (R k) (H k) s k j (by omega) ho hkj
      (hgood k hk ho).1 (hgood k hk ho).2.1 (hgood k hk ho).2.2.1 hs (hgood k hk ho).2.2.2
  rw [hdec (n + 4 * p) (by omega) hodd2 hj,
    hdec (n + 2 * p) (by omega) hodd1 hj1, hdec n le_rfl hnodd hj0]
  have ha := alpha_even_step_second_difference n p hnodd
  have har : (alpha (n + 4 * p) : ℝ) + alpha n =
      2 * alpha (n + 2 * p) + ((2 * p : ℕ) : ℝ)^2 := by exact_mod_cast ha
  have he := entropyPart_second_difference_upper n (2 * p) (by omega)
  have ht := log_tau_second_difference_nonneg n (2 * p) hn
  have hstep : 2 * (2 * p) = 4 * p := by ring
  rw [hstep] at he ht
  have hg := (gammaCorrection_alpha_second_difference_bounds n p hnodd j (by exact_mod_cast hj)).2
  have hE0 := abs_le.mp (herr n le_rfl hnodd)
  have hE1 := abs_le.mp (herr (n + 2 * p) (by omega) hodd1)
  have hE2 := abs_le.mp (herr (n + 4 * p) (by omega) hodd2)
  have hmul := mul_nonneg (show (0 : ℝ) ≤ j by positivity) ht
  have hqa := congrArg (fun x : ℝ => x * (modelQuadraticConstant B0 s - Real.log j)) har
  push_cast at hqa he hg ⊢
  nlinarith [hE0.2, hE1.1, hE2.2]

end
end IsingBulk.Anisotropic.NegativeDominance
