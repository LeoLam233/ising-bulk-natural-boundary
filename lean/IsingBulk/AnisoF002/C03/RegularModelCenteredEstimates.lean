import IsingBulk.AnisoF002.C03.RegularModelFiniteDifferences

/-!
# Actual-model crossing and discrete-curvature estimates

The constants are constructed from B's analytic germ and the fixed even
particle step.  Nonvanishing of every genuine model factor is derived
internally.  The half-order gamma range is explicit; it contains the
entire asymptotic window used for the integer-order crossing selection.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

theorem actual_model_centered_estimates {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c : ℝ) {s : ℝ} (hs : 0 < s)
    (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ n j : ℕ, Odd n → R ≤ (n : ℝ) + d →
      2 * (particleExponent (n + 2 * d) : ℝ) ≤ j →
      |(actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j) / (2 * (d : ℝ)) -
        (2 * (j : ℝ) / ((n : ℝ) + d) - ((n : ℝ) + d) * Real.log j)| ≤
          C * (((n : ℝ) + d) + ((n : ℝ) + d) ^ 3 / j + (j : ℝ) / ((n : ℝ) + d) ^ 3) ∧
      |actualModelLog B c s (n + 2 * d) j - 2 * actualModelLog B c s (n + d) j + actualModelLog B c s n j +
        (d : ℝ) ^ 2 * (2 * (j : ℝ) / ((n : ℝ) + d) ^ 2 + Real.log j)| ≤
          C * (1 + ((n : ℝ) + d) ^ 2 / j + (j : ℝ) / ((n : ℝ) + d) ^ 4) := by
  obtain ⟨C₀, R₀, hC₀, hR₀, hcorr⟩ := actual_model_correction_differences hB hslit c s
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_actual_model_factors_ne_zero hB.continuousAt (Complex.slitPlane_ne_zero hslit) c s)
  let R := max R₀ (max (4 * (d : ℝ) + 1) ((N : ℝ) + d))
  let A₁ := modelFirstLinearConstant C₀ d
  let A₂ := modelSecondConstant C₀ d
  let H₁ := modelFirstOrderConstant C₀ d
  let H₂ := modelSecondOrderConstant C₀ d
  let C := 1 + A₁ + A₂ + H₁ + H₂ + 8 * (d : ℝ) + 6 * (d : ℝ) ^ 2
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁, modelFirstLinearConstant]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂, modelSecondConstant]; positivity
  have hH₁ : 0 ≤ H₁ := by dsimp [H₁, modelFirstOrderConstant]; positivity
  have hH₂ : 0 ≤ H₂ := by dsimp [H₂, modelSecondOrderConstant]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hR : 0 < R := hR₀.trans_le (le_max_left _ _)
  have hCA₁ : A₁ ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  have hCA₂ : A₂ ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  have hCH₁ : H₁ ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  have hCH₂ : H₂ ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  have hCd₁ : 8 * (d : ℝ) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  have hCd₂ : 6 * (d : ℝ) ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (d : ℝ)]
  refine ⟨C, R, hC, hR, ?_⟩
  intro n j hn hlarge hrange
  let x : ℝ := (n : ℝ) + d
  have hx : 0 < x := hR.trans_le hlarge
  have hR₀x : R₀ ≤ x := (le_max_left _ _).trans hlarge
  have hdx : 4 * (d : ℝ) + 1 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hstep : (d : ℝ) ≤ x / 4 := by linarith
  have hNn : N ≤ n := by
    have hh : (N : ℝ) + d ≤ x :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
    exact_mod_cast (show (N : ℝ) ≤ n by dsimp [x] at hh; linarith)
  have hfactors : ∀ k ∈ ({n, n + d, n + 2 * d} : Finset ℕ),
      B (windingTau k : ℂ) ≠ 0 ∧ firstWindingCurvature k (B (windingTau k : ℂ)) c s ≠ 0 := by
    intro k hk
    have hnk : n ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    exact (hN k (hNn.trans hnk)).2
  have hαpos : 0 < particleExponent (n + 2 * d) := by
    have hge : 3 ≤ n + 2 * d := by have := hn.pos; omega
    have hpow : 9 ≤ (n + 2 * d) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  have hj : 0 < j := by
    have ha : 0 < (particleExponent (n + 2 * d) : ℝ) := by exact_mod_cast hαpos
    exact_mod_cast (show (0 : ℝ) < j by linarith)
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hfinite := actual_model_finite_differences n d j hn hd hs hj hstep hrange hfactors
    (hcorr n d hn hd hR₀x hstep)
  have hfirst : |actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j -
      2 * (d : ℝ) * (2 * (j : ℝ) / x - x * Real.log j)| ≤
      C * (x + x ^ 3 / j + (j : ℝ) / x ^ 3) := by
    apply hfinite.1.trans
    change A₁ * x + 8 * (d : ℝ) * x ^ 3 / j + H₁ * (j : ℝ) / x ^ 3 ≤ _
    calc
      _ = A₁ * x + (8 * (d : ℝ)) * (x ^ 3 / j) + H₁ * ((j : ℝ) / x ^ 3) := by ring
      _ ≤ C * x + C * (x ^ 3 / j) + C * ((j : ℝ) / x ^ 3) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCA₁ hx.le)
          (mul_le_mul_of_nonneg_right hCd₁ (by positivity)))
          (mul_le_mul_of_nonneg_right hCH₁ (by positivity))
      _ = _ := by ring
  constructor
  · have he : (actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j) / (2 * (d : ℝ)) -
        (2 * (j : ℝ) / x - x * Real.log j) =
        (actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j -
          2 * (d : ℝ) * (2 * (j : ℝ) / x - x * Real.log j)) / (2 * (d : ℝ)) := by
      field_simp
    rw [he, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * (d : ℝ))]
    apply (div_le_div_of_nonneg_right hfirst (by positivity : 0 ≤ 2 * (d : ℝ))).trans
    apply div_le_self (by positivity)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    linarith
  · apply hfinite.2.trans
    change A₂ + 6 * (d : ℝ) ^ 2 * x ^ 2 / j + H₂ * (j : ℝ) / x ^ 4 ≤ _
    calc
      _ = A₂ + (6 * (d : ℝ) ^ 2) * (x ^ 2 / j) + H₂ * ((j : ℝ) / x ^ 4) := by ring
      _ ≤ C + C * (x ^ 2 / j) + C * ((j : ℝ) / x ^ 4) :=
        add_le_add (add_le_add hCA₂ (mul_le_mul_of_nonneg_right hCd₂ (by positivity)))
          (mul_le_mul_of_nonneg_right hCH₂ (by positivity))
      _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
