import IsingBulk.AnisoF002.RegularTail.FiniteNumerator

/-!
# Exact one-body and pair normalization in the finite numerator

Frozen/published `eq:corrFF`, `eq:cancelpair`, and `eq:fullangular`.
These identities retain the complete B-power. They identify the actual
finite numerator on any selected logarithmic branch. No infinite sum or
field response is supplied by these finite algebraic identities.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

theorem exp_sinh_denominator (γ : ℂ) :
    1 - Complex.exp (-γ) ^ 2 = 2 * Complex.exp (-γ) * Complex.sinh γ := by
  rw [Complex.sinh, Complex.exp_neg]
  field_simp

theorem oneBody_exp_eq_inv_sinh (γ : ℂ) :
    2 * Complex.exp (-γ) / (1 - Complex.exp (-γ) ^ 2) = 1 / Complex.sinh γ := by
  rw [exp_sinh_denominator]
  by_cases hs : Complex.sinh γ = 0
  · simp [hs]
  · field_simp

theorem sinePairCoefficient_exp (B γ η : ℂ) :
    sinePairCoefficient B (Complex.exp (-γ)) (Complex.exp (-η)) =
      B / Complex.sinh ((γ + η) / 2) ^ 2 := by
  have he : Complex.exp (-γ) * Complex.exp (-η) =
      Complex.exp (-((γ + η) / 2)) ^ 2 := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold sinePairCoefficient
  rw [mul_assoc (4 * B), he, exp_sinh_denominator]
  by_cases hs : Complex.sinh ((γ + η) / 2) = 0
  · simp [hs]
  · field_simp
    ring

/-- N one-body square-root factors and all N(N-1)/2 pair factors give the
literal B^(N²/2), represented without fractional-power ambiguity as b^(N²). -/
theorem complete_anisotropy_power (N : ℕ) (b B : ℂ) (hb : b ^ 2 = B) :
    b ^ N * B ^ (N.choose 2) = b ^ (N ^ 2) := by
  rw [← hb, ← pow_mul, ← pow_add]
  congr 1
  cases N with
  | zero => simp
  | succ n =>
    have hc := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right] at hc
    change (n + 1) + 2 * (n + 1).choose 2 = (n + 1) ^ 2
    nlinarith

/-- Exact complete finite numerator on any chosen logarithmic branch of
the actual canonical roots. The exponent uses that branch's square root b.
The hypothesis does not cover a root zero, where the separate HT origin
formula is still required. -/
theorem fullRootNumeratorF002_log_branch {N : ℕ} (lam : ℝ) (z b : ℂ)
    (q : Fin N → ℝ) (γ : Fin N → ℂ)
    (hγ : ∀ i, spectralSmallRootF002 lam z (q i) = Complex.exp (-γ i))
    (hb : b ^ 2 = IsingBulk.Anisotropic.spectralT lam z /
      IsingBulk.Anisotropic.spectralS z) :
    fullRootNumeratorF002 lam z b q =
      b ^ (N ^ 2) * (∏ i, 1 / Complex.sinh (γ i)) *
        ∏ ij ∈ indexPairs N,
          ((Real.sin ((q ij.1 - q ij.2) / 2) : ℂ) /
            Complex.sinh ((γ ij.1 + γ ij.2) / 2)) ^ 2 := by
  let B := IsingBulk.Anisotropic.spectralT lam z / IsingBulk.Anisotropic.spectralS z
  have hone (i : Fin N) : spectralOneBodyF002 lam z (q i) = 1 / Complex.sinh (γ i) := by
    unfold spectralOneBodyF002
    rw [hγ i, oneBody_exp_eq_inv_sinh]
  have hpair (ij : Fin N × Fin N) : spectralCanceledPairF002 lam z (q ij.1) (q ij.2) =
      B * (((Real.sin ((q ij.1 - q ij.2) / 2) : ℂ) /
        Complex.sinh ((γ ij.1 + γ ij.2) / 2)) ^ 2) := by
    rw [spectralCanceledPairF002_factorization]
    unfold spectralSinePairCoefficientF002
    rw [hγ ij.1, hγ ij.2, sinePairCoefficient_exp]
    change B / _ ^ 2 * _ = _
    rw [div_pow, Complex.ofReal_pow]
    ring
  have he : fullRootNumeratorF002 lam z b q =
      (b ^ N * B ^ (N.choose 2)) * (∏ i, 1 / Complex.sinh (γ i)) *
        ∏ ij ∈ indexPairs N,
          ((Real.sin ((q ij.1 - q ij.2) / 2) : ℂ) /
            Complex.sinh ((γ ij.1 + γ ij.2) / 2)) ^ 2 := by
    unfold fullRootNumeratorF002
    simp_rw [hone, hpair]
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs]
    ring
  rw [he, complete_anisotropy_power N b B hb]

end
end IsingBulk.AnisoF002.RegularTail
