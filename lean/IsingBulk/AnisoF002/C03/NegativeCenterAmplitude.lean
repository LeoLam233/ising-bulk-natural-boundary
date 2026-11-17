import IsingBulk.AnisoF002.C03.NegativeActualPoleDensityGeometry

/-!
# Exact complete center amplitude

The physical square root is kept as an explicit b with b²=B.  Thus the
half-integral power in frozen (4.12) is evaluated on that same physical
branch, never silently replaced by a principal complex power.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators

theorem twice_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ k =>
    have hh := Nat.add_one_mul_choose_eq k 1
    simp only [Nat.choose_one_right] at hh
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, mul_comm] using hh.symm

theorem one_body_pair_degree (n : ℕ) : n + 2 * n.choose 2 = n ^ 2 := by
  cases n with
  | zero => simp
  | succ k =>
    rw [twice_choose_two]
    simp only [Nat.add_sub_cancel]
    ring

theorem imaginary_odd_square (n : ℕ) (hn : Odd n) : Complex.I ^ (n ^ 2) = Complex.I := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring, pow_add, pow_mul]
  norm_num

theorem complete_center_hyperbolic_factors (n : ℕ) (hn : Odd n)
    (s : ℂ) (hs : s ≠ 0) :
    (1 / (s * Complex.I)) ^ n * (1 / (2 * (s * Complex.I))) ^ (2 * n.choose 2) =
      -Complex.I / ((2 : ℂ) ^ (n * (n - 1)) * s ^ (n ^ 2)) := by
  have hdeg := one_body_pair_degree n
  calc
    _ = 1 / ((s * Complex.I) ^ n * (2 * (s * Complex.I)) ^ (2 * n.choose 2)) := by
      simp only [one_div_pow]
      ring
    _ = 1 / ((2 : ℂ) ^ (2 * n.choose 2) * (s * Complex.I) ^ (n + 2 * n.choose 2)) := by
      rw [pow_add, mul_pow]
      ring
    _ = 1 / ((2 : ℂ) ^ (n * (n - 1)) * (s ^ (n ^ 2) * Complex.I)) := by
      rw [hdeg, twice_choose_two, mul_pow, imaginary_odd_square n hn]
    _ = _ := by
      field_simp
      simp

theorem filledNegativeNumerator_odd_center (n : ℕ) (hn : Odd n)
    (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (τ d : ℂ) (φ : ℝ)
    (hφ : Real.sin φ ≠ 0) (hcenter : g (τ, d) = (φ : ℂ) * Complex.I) :
    filledNegativeNumerator n b g d τ 0 =
      -Complex.I * b τ ^ (n ^ 2) /
        (windingNormalization n * (2 : ℂ) ^ (n * (n - 1)) * (Real.sin φ : ℂ) ^ (n ^ 2)) := by
  rw [filledNegativeNumerator_center n b g d τ ((φ : ℂ) * Complex.I) hcenter,
    Complex.sinh_mul_I, ← Complex.ofReal_sin]
  rw [mul_assoc, complete_center_hyperbolic_factors n hn (Real.sin φ : ℂ)
    (by exact_mod_cast hφ)]
  ring

theorem filledNegativeDensity_exact_center (n : ℕ) (hn : Odd n) (hn2 : 2 ≤ n)
    (b B : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (φ d : ℝ)
    (hφ : Real.sin φ ≠ 0)
    (hB : AnalyticAt ℂ B ((1 - Real.cos d : ℝ) : ℂ))
    (hBne : B ((1 - Real.cos d : ℝ) : ℂ) ≠ 0)
    (hb : b ((1 - Real.cos d : ℝ) : ℂ) ^ 2 = B ((1 - Real.cos d : ℝ) : ℂ))
    (hga : AnalyticAt ℂ g ((1 - Real.cos d : ℝ), (d : ℂ)))
    (hgv : g ((1 - Real.cos d : ℝ), (d : ℂ)) = (φ : ℂ) * Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((1 - Real.cos d : ℝ), (d : ℂ)),
      Complex.cosh (g a) = localNegativeDispersion B φ a) :
    filledNegativeDensityAt n b g (d : ℂ) ((1 - Real.cos d : ℝ) : ℂ) 0 =
      -(2 * b ((1 - Real.cos d : ℝ) : ℂ) ^ (n ^ 2 - 2)) /
        ((n : ℂ) * windingNormalization n * (2 : ℂ) ^ (n * (n - 1)) *
          (Real.sin φ : ℂ) ^ (n ^ 2 - 1)) := by
  have hd := local_negative_phase_derivative_unique B φ d hφ hB hga hgv hge
  have hc : phaseTemperatureDerivative g ((1 - Real.cos d : ℝ), (d : ℂ)) =
      ((Real.sin φ : ℂ) * Complex.I)⁻¹ * B ((1 - Real.cos d : ℝ) : ℂ) := by
    simpa [phaseTemperatureDerivative] using
      congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1, 0)) hd.fderiv
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnSq : 2 ≤ n ^ 2 := by nlinarith
  have hs : (Real.sin φ : ℂ) ≠ 0 := by exact_mod_cast hφ
  have hW := windingNormalization_ne_zero n
  have hpb : b ((1 - Real.cos d : ℝ) : ℂ) ^ (n ^ 2) =
      b ((1 - Real.cos d : ℝ) : ℂ) ^ (n ^ 2 - 2) * B ((1 - Real.cos d : ℝ) : ℂ) := by
    rw [← hb, ← pow_add, Nat.sub_add_cancel hnSq]
  have hps : (Real.sin φ : ℂ) ^ (n ^ 2) =
      (Real.sin φ : ℂ) ^ (n ^ 2 - 1) * (Real.sin φ : ℂ) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n ^ 2)]
  unfold filledNegativeDensityAt
  rw [filledNegativeNumerator_odd_center n hn b g _ _ φ hφ hgv,
    phaseTemperatureSum_center, hc, hpb, hps]
  field_simp
  ring_nf
  norm_num

end
end IsingBulk.AnisoF002.NegativeHT
