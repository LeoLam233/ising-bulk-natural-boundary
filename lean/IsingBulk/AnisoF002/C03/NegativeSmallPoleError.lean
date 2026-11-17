import IsingBulk.AnisoF002.C03.NegativeActualHigherError

/-!
# A fixed-radius quarter-error bound and the true pole denominator

The full cubic/quartic remainder is made small on one fixed Q-ball.
The positive real quadratic model then controls the actual complex pole;
this supplies the nonvanishing denominator needed in the real-cycle
integrals, including the center itself.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem displacement_moment_bound (n k : ℕ) (v : Fin n → ℂ) {σ : ℝ}
    (_hσ : 0 ≤ σ) (hv : ∀ i, ‖v i‖ ≤ σ) :
    (∑ i, ‖v i‖ ^ (k + 2)) ≤ σ ^ k * displacementSquare n v := by
  calc
    _ = ∑ i, ‖v i‖ ^ k * ‖v i‖ ^ 2 := by simp only [pow_add]
    _ ≤ ∑ i, σ ^ k * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hv i
    _ = _ := by rw [← Finset.mul_sum]; rfl

set_option maxHeartbeats 1000000 in
theorem higher_pole_error_small (n : ℕ) (hn : 0 < n) (v : Fin n → ℂ)
    {K σ : ℝ} (hK : 0 ≤ K) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hKσ : 48 * K * σ ≤ 1) (hQ : displacementSquare n v < σ ^ 2)
    {T T₀ : ℂ}
    (herr : ‖T - T₀‖ ≤ K / (n : ℝ) *
      ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
        displacementSquare n v ^ 2 / (n : ℝ))) :
    ‖T - T₀‖ ≤ displacementSquare n v / (16 * (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hQ0 := displacementSquare_nonneg n v
  have hv (i : Fin n) : ‖v i‖ ≤ σ := by
    have hi : ‖v i‖ ^ 2 ≤ displacementSquare n v :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have h₃ : (∑ i, ‖v i‖ ^ 3) ≤ σ * displacementSquare n v := by
    simpa only [pow_one] using displacement_moment_bound n 1 v hσ.le hv
  have h₄ := displacement_moment_bound n 2 v hσ.le hv
  have h₃div : (∑ i, ‖v i‖ ^ 3) / (n : ℝ) ≤ σ * displacementSquare n v :=
    (div_le_self (by positivity) hn1).trans h₃
  have hQdiv : displacementSquare n v ^ 2 / (n : ℝ) ≤ σ ^ 2 * displacementSquare n v :=
    (div_le_self (sq_nonneg _) hn1).trans (by nlinarith)
  have hbudget : (∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
      displacementSquare n v ^ 2 / (n : ℝ) ≤ 3 * σ * displacementSquare n v := by
    have hs : σ ^ 2 ≤ σ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs hQ0]
  calc
    ‖T - T₀‖ ≤ K / (n : ℝ) * (3 * σ * displacementSquare n v) :=
      herr.trans (mul_le_mul_of_nonneg_left hbudget (div_nonneg hK hnR.le))
    _ = (3 * K * σ) * displacementSquare n v / (n : ℝ) := by ring
    _ ≤ (1 / 16 : ℝ) * displacementSquare n v / (n : ℝ) := by gcongr; nlinarith
    _ = _ := by ring

theorem actual_pole_quarter_control {N τ Q : ℝ} {h T : ℂ}
    (hN : 0 < N) (hτ : 0 < τ) (hQ : 0 ≤ Q) (hh : (1 / 2 : ℝ) ≤ h.re)
    (herr : ‖T - ((τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ))‖ ≤ Q / (16 * N)) :
    let D := τ + h.re * Q / (2 * N)
    let T₀ := (τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ)
    ‖T - T₀‖ ≤ D / 4 ∧ D ≤ ‖T₀‖ ∧ 3 * D / 4 ≤ ‖T‖ ∧ T ≠ 0 := by
  dsimp only
  have hDpos : 0 < τ + h.re * Q / (2 * N) :=
    add_pos_of_pos_of_nonneg hτ (by positivity)
  have hDlower : Q / (4 * N) ≤ τ + h.re * Q / (2 * N) := by
    have hc : (1 / 2 : ℝ) * Q / (2 * N) ≤ h.re * Q / (2 * N) := by gcongr
    have he : (1 / 2 : ℝ) * Q / (2 * N) = Q / (4 * N) := by ring
    rw [he] at hc
    linarith
  have hquarter : ‖T - ((τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ))‖ ≤
      (τ + h.re * Q / (2 * N)) / 4 := by
    apply herr.trans
    have hh' := div_le_div_of_nonneg_right hDlower (by norm_num : (0 : ℝ) ≤ 4)
    convert hh' using 1
    ring
  have hmodel : τ + h.re * Q / (2 * N) ≤
      ‖(τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ)‖ := by
    have he : ((τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ)).re =
        τ + h.re * Q / (2 * N) := by
      rw [Complex.add_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [← he]
    exact Complex.re_le_norm _
  have hnorm : 3 * (τ + h.re * Q / (2 * N)) / 4 ≤ ‖T‖ := by
    have ht := norm_le_norm_add_norm_sub T ((τ : ℂ) + h * ((Q / (2 * N) : ℝ) : ℂ))
    linarith
  refine ⟨hquarter, hmodel, hnorm, ?_⟩
  exact norm_pos_iff.mp ((by linarith : 0 < 3 * (τ + h.re * Q / (2 * N)) / 4).trans_le hnorm)

end
end IsingBulk.AnisoF002.NegativeHT
