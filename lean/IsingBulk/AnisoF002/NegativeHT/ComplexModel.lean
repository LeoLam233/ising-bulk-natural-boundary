import IsingBulk.AnisoF002.NegativeHT.ExactFactors

/-!
# F002's complex first-winding model and its exact modulus

This is the full displayed model M(n,j), including its sign and the complex
powers of B_n and h_n. Equality with the actual localized physical integral
is deliberately not asserted here; that requires the real-cycle remainder,
angular concentration, and beta-period analysis.
-/

namespace IsingBulk.AnisoF002.NegativeHT

noncomputable section

/-- The normalized complex first-winding model. Real powers are used for
positive scalar factors; the B and h factors retain their complex phases. -/
def modelCoefficient (n j : ℕ) (B h : ℂ) (s τ : ℝ) : ℂ :=
  -(((2:ℝ)^(2-(particleExponent n:ℝ)):ℝ):ℂ) *
    B^(((particleExponent n:ℝ)-1/2:ℝ):ℂ) *
    (factorialProduct n:ℂ) *
    (((n:ℝ)^((particleExponent n:ℝ)-3/2):ℝ):ℂ) /
      ((Real.pi^(((n:ℝ)-1)/2) * s^(2*particleExponent n):ℝ):ℂ) *
    h^((-(particleExponent n:ℝ):ℝ):ℂ) *
    ((τ^(particleExponent n)/τ^(j+1)*gammaQuotient j (particleExponent n):ℝ):ℂ)

/-- The modulus calculation retains every scalar and particle normalization.
There is no common-phase premise on B or h. -/
theorem norm_modelCoefficient (n j : ℕ) (B h : ℂ) (s τ : ℝ)
    (hn : 0<n) (hs : 0<s) (hτ : 0<τ) :
    ‖modelCoefficient n j B h s τ‖ = modelMagnitude n j ‖B‖ ‖h‖ s τ := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hp := factorialProduct_pos n
  have h2 : (0:ℝ)<(2:ℝ)^(2-(particleExponent n:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hnp : (0:ℝ)<(n:ℝ)^((particleExponent n:ℝ)-3/2) := Real.rpow_pos_of_pos hn' _
  have hpi : (0:ℝ)<Real.pi^(((n:ℝ)-1)/2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hsp : (0:ℝ)<s^(2*particleExponent n) := pow_pos hs _
  have hta : (0:ℝ)<τ^(particleExponent n) := pow_pos hτ _
  have htj : (0:ℝ)<τ^(j+1) := pow_pos hτ _
  have hγ := gammaQuotient_pos j (particleExponent n)
  simp only [modelCoefficient, norm_mul, norm_div, norm_neg, Complex.norm_cpow_real,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos h2, abs_of_pos hp, abs_of_pos hnp, abs_of_pos hpi, abs_of_pos hsp,
    abs_of_pos hta, abs_of_pos htj, abs_of_pos hγ]
  unfold modelMagnitude modelPrefactor
  ring

/-- The model has nonzero modulus for the physical nonzero B,h and positive
s,tau parameters. Cancellation can therefore only arise at the series level. -/
theorem modelCoefficient_ne_zero (n j : ℕ) (B h : ℂ) (s τ : ℝ)
    (hn : 0<n) (hB : B≠0) (hh : h≠0) (hs : 0<s) (hτ : 0<τ) :
    modelCoefficient n j B h s τ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_modelCoefficient n j B h s τ hn hs hτ]
  exact modelMagnitude_pos n j ‖B‖ ‖h‖ s τ hn (norm_pos_iff.mpr hB)
    (norm_pos_iff.mpr hh) hs hτ

end

end IsingBulk.AnisoF002.NegativeHT
