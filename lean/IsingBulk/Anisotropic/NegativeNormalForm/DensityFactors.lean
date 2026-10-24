import IsingBulk.Anisotropic.NegativeNormalForm.PoleSeparableMap
import IsingBulk.Anisotropic.NegativeNormalForm.Vandermonde
import IsingBulk.Anisotropic.NegativeDominance.ExactModel

/-! The complete form-factor numerator and pole residue, with the Vandermonde
removed by actual analytic sine divided differences, including all coincidences.
No Jacobian or dimension-uniform estimate is silently included here. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators Topology
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance

def halfSineSlope (z : ℂ) : ℂ := dslope Complex.sin 0 (z/2)/2

@[simp] theorem halfSineSlope_zero : halfSineSlope 0 = 1/2 := by
  simp [halfSineSlope, dslope_same]

theorem halfSineSlope_mul (z : ℂ) : z * halfSineSlope z = Complex.sin (z/2) := by
  have h := sub_smul_dslope Complex.sin 0 (z/2)
  simpa [halfSineSlope, smul_eq_mul, mul_div_assoc, div_mul_eq_mul_div] using h

theorem halfSineSlope_analyticAt : AnalyticAt ℂ halfSineSlope 0 := by
  have h := analyticAt_dslope_center (show AnalyticAt ℂ Complex.sin 0 from Complex.analyticAt_sin)
  have hc : AnalyticAt ℂ (fun z : ℂ => z/2) 0 := analyticAt_id.div_const
  exact (h.comp_of_eq hc (by simp)).div_const

def densityPrefactor (B rootB : ℂ → ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  rootB t * B t ^ alpha n / ((n.factorial : ℂ)*(2*(Real.pi : ℂ))^(n-1))

def pairDenominator (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t x y : ℂ) : ℂ :=
  Complex.sinh ((negativePhase B phi hphi t (d+x)+negativePhase B phi hphi t (d+y))/2)

def formFactorNumerator {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) : ℂ :=
  densityPrefactor B rootB n t *
    (∏ i, (Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹) *
    ∏ p ∈ firstStrictPairs n,
      (Complex.sin ((v p.1-v p.2)/2) / pairDenominator B phi hphi d t (v p.1) (v p.2))^2

def regularNumerator {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) : ℂ :=
  densityPrefactor B rootB n t *
    (∏ i, (Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹) *
    ∏ p ∈ firstStrictPairs n,
      (halfSineSlope (v p.1-v p.2) / pairDenominator B phi hphi d t (v p.1) (v p.2))^2

/-- Exact factorization without division by Δ, valid on every coincidence divisor. -/
theorem formFactorNumerator_factor {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) :
    formFactorNumerator B rootB phi hphi d t v =
      vandermonde v^2 * regularNumerator B rootB phi hphi d t v := by
  have hp : (∏ p ∈ firstStrictPairs n,
      (Complex.sin ((v p.1-v p.2)/2) / pairDenominator B phi hphi d t (v p.1) (v p.2))^2) =
      vandermonde v^2 * ∏ p ∈ firstStrictPairs n,
      (halfSineSlope (v p.1-v p.2) / pairDenominator B phi hphi d t (v p.1) (v p.2))^2 := by
    rw [vandermonde, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [← halfSineSlope_mul]
    ring
  rw [formFactorNumerator, hp, regularNumerator]
  ring

def poleParameterDerivative {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) : ℂ :=
  deriv (fun u => poleEquation B phi hphi d u v) t

def poleResidue {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config n → ℂ) (v : Config n) : ℂ :=
  -2*formFactorNumerator B rootB phi hphi d (T v) v /
    poleParameterDerivative B phi hphi d (T v) v

def regularResidue {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config n → ℂ) (v : Config n) : ℂ :=
  -2*regularNumerator B rootB phi hphi d (T v) v /
    poleParameterDerivative B phi hphi d (T v) v

theorem poleResidue_factor {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config n → ℂ) (v : Config n) :
    poleResidue B rootB phi hphi d T v =
      vandermonde v^2 * regularResidue B rootB phi hphi d T v := by
  rw [poleResidue, formFactorNumerator_factor, regularResidue]
  ring

/-- Central regular numerator before the elementary odd-particle power simplification. -/
theorem regularNumerator_center {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    regularNumerator B rootB phi hphi d (1-Complex.cos d) (0 : Config n) =
      densityPrefactor B rootB n (1-Complex.cos d) *
      (((Real.sin phi : ℂ)*Complex.I)⁻¹)^n *
      ((1/2)/((Real.sin phi : ℂ)*Complex.I))^(2*(n.choose 2)) := by
  have hs : ((phi : ℂ)*Complex.I+(phi : ℂ)*Complex.I)/2 = (phi : ℂ)*Complex.I := by ring
  simp only [regularNumerator, Pi.zero_apply, add_zero, sub_self, halfSineSlope_zero,
    pairDenominator, negativePhase_center, hs, Complex.sinh_mul_I, ← Complex.ofReal_sin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, firstStrictPairs_card, ← pow_mul]

theorem regularResidue_center {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (T : Config n → ℂ) (hT : T 0 = 1-Complex.cos d) :
    regularResidue B rootB phi hphi d T 0 =
      -2*(densityPrefactor B rootB n (1-Complex.cos d) *
      (((Real.sin phi : ℂ)*Complex.I)⁻¹)^n *
      ((1/2)/((Real.sin phi : ℂ)*Complex.I))^(2*(n.choose 2))) /
      (n * (((Real.sin phi : ℂ)*Complex.I)⁻¹*B (1-Complex.cos d))) := by
  rw [regularResidue, hT, regularNumerator_center]
  congr 1
  exact (poleEquation_hasDerivAt_center (n := n) B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv

end
end IsingBulk.Anisotropic.NegativeNormalForm
