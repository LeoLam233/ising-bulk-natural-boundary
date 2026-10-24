import IsingBulk.Anisotropic.NegativeDominance.CollisionPowers
import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors

/-! Algebraic normalization of the actual central residue. This does not
assert the missing full Jacobian or identification of actual winding jets. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm

theorem collision_inverse_product (s : ℂ) (n : ℕ) (hn : Odd n) (hs : s ≠ 0) :
    (((s * Complex.I)⁻¹)^n * ((1 / 2) / (s * Complex.I))^(2 * n.choose 2)) /
      (s * Complex.I)⁻¹ = 1 / ((2 : ℂ)^(2 * n.choose 2) * s^(2 * alpha n)) := by
  have hS : s * Complex.I ≠ 0 := mul_ne_zero hs Complex.I_ne_zero
  have hp : (s * Complex.I)^n * (s * Complex.I)^(2 * n.choose 2) =
      s^(2 * alpha n) * (s * Complex.I) := by
    rw [← pow_add, odd_collision_degree n hn, pow_succ, imaginary_collision_power s n hn]
  simp only [div_pow, one_div, inv_pow]
  field_simp [hs, hS]
  linear_combination -hp

theorem root_power_quotient (B rootB : ℂ) (a : ℕ) (hB : B ≠ 0) (hr : rootB ≠ 0)
    (hsq : rootB^2 = B) : rootB * B^a / B = B^a / rootB := by
  field_simp
  exact hsq

def centralDensity (Bn rootBn : ℂ) (s : ℝ) (n : ℕ) : ℂ :=
  -2 * (Bn ^ alpha n / rootBn) /
    ((n : ℂ) * (n.factorial : ℂ) * (2 * (Real.pi : ℂ))^(n-1) *
      (2 : ℂ)^(n*(n-1)) * (s : ℂ)^(2 * alpha n))

/-- The full central regular residue, including its sign and all factorial,
angular, and physical square-root factors, equals (4.39). -/
theorem regularResidue_center_normalized {n : ℕ} (hn : Odd n)
    (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1 - Complex.cos d))
    (T : Config n → ℂ) (hT : T 0 = 1 - Complex.cos d)
    (hBn : B (1 - Complex.cos d) ≠ 0) (hr : rootB (1 - Complex.cos d) ≠ 0)
    (hsq : rootB (1 - Complex.cos d)^2 = B (1 - Complex.cos d)) :
    regularResidue B rootB phi hphi d T 0 =
      centralDensity (B (1 - Complex.cos d)) (rootB (1 - Complex.cos d)) (Real.sin phi) n := by
  rw [regularResidue_center B rootB phi hphi d hB T hT]
  have hs : ((Real.sin phi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hphi
  have hS : (Real.sin phi : ℂ) * Complex.I ≠ 0 := mul_ne_zero hs Complex.I_ne_zero
  have hnpos : 0 < n := by obtain ⟨k, rfl⟩ := hn; omega
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  let P := densityPrefactor B rootB n (1 - Complex.cos d)
  let S : ℂ := (Real.sin phi : ℂ) * Complex.I
  let Q : ℂ := (S⁻¹)^n * ((1 / 2) / S)^(2 * n.choose 2) / S⁻¹
  have hQ : Q = 1 / ((2 : ℂ)^(2 * n.choose 2) * (Real.sin phi : ℂ)^(2 * alpha n)) :=
    collision_inverse_product _ n hn hs
  change -2 * (P * (S⁻¹)^n * ((1 / 2) / S)^(2 * n.choose 2)) /
    (n * (S⁻¹ * B (1 - Complex.cos d))) = _
  have he : -2 * (P * (S⁻¹)^n * ((1 / 2) / S)^(2 * n.choose 2)) /
      (n * (S⁻¹ * B (1 - Complex.cos d))) =
      (-2 * P / ((n : ℂ) * B (1 - Complex.cos d))) * Q := by
    dsimp [Q, S]
    field_simp
  rw [he, hQ, odd_two_mul_choose_two n hn]
  dsimp [P, densityPrefactor, centralDensity]
  field_simp
  rw [hsq]

end
end IsingBulk.Anisotropic.NegativeDominance
