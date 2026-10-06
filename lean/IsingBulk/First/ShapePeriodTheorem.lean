import IsingBulk.First.ScalarBeta
import IsingBulk.First.ShapeRadialContinuation
import IsingBulk.First.ShapeArithmetic
import IsingBulk.First.FirstCoefficient

/-! The source constrained shape period: exact beta evaluation and nonvanishing. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

theorem shapeRadialIntegral_boundary_beta (k : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) :
    shapeRadialIntegral k Q (-Complex.I*d) = shapeRadialValue k Q (-Complex.I*d) := by
  apply shapeRadialIntegral_boundary_eq_of_positive k hQ hd
  intro c hc
  exact shapeRadialIntegral_positive_beta k hQ hc

/-- Exact beta evaluation for the actual constrained coordinate integral. -/
theorem shapePeriod_eq_beta {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q d : ℝ} (hQ : 0 < Q) (hd : 0 < d) :
    shapePeriod n k Q (-Complex.I*d) =
      (shapeAngularConstant n : ℂ)/2 * (Q : ℂ)^(-1/2 : ℂ) *
        (-Complex.I*d)^(-(k : ℂ)-1/2) *
        Complex.betaIntegral ((k : ℂ)+1/2) (1/2) := by
  rw [shapePeriod_eq_radial hn hdegree, shapeRadialIntegral_boundary_beta k hQ hd]
  simp only [Complex.real_smul, shapeRadialValue]
  ring

theorem shapePeriod_ne_zero {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q d : ℝ} (hQ : 0 < Q) (hd : 0 < d) :
    shapePeriod n k Q (-Complex.I*d) ≠ 0 := by
  rw [shapePeriod_eq_radial hn hdegree, shapeRadialIntegral_boundary_beta k hQ hd]
  exact smul_ne_zero (shapeAngularConstant_pos hn).ne'
    (shapeRadialValue_ne_zero k hQ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hd.ne')))

/-- Source-facing period endpoint for N=n+1 even and k=N²/2−1. It gives
absolute convergence, the displayed a₀-formula, and actual nonvanishing.
All hypotheses are preceding dimension and positive quadratic-coefficient data. -/
theorem lemma_period {n : ℕ} (hn : 1 ≤ n) (he : Even (n+1)) {Q d : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) :
    let k := (n+1)^2/2-1
    let a₀ : ℂ := (((n+1 : ℕ) : ℂ)^2-1)/2
    Integrable (fun t : Fin n → ℝ =>
      let x := shapeCoordinateEquiv n (WithLp.toLp 2 t)
      (shapeVandermondeSq x : ℂ) / ((Q : ℂ) - Complex.I*d*(‖x‖ : ℂ)^2)^(k+1)) ∧
    shapePeriod n k Q (-Complex.I*d) =
      (shapeAngularConstant n : ℂ)/2 * (Q : ℂ)^(-1/2 : ℂ) *
        (-Complex.I*d)^(-a₀) * Complex.betaIntegral a₀ (1/2) ∧
    shapePeriod n k Q (-Complex.I*d) ≠ 0 := by
  dsimp only
  have hexp := source_shape_radial_exponent hn he
  have ha : (((((n+1)^2/2-1 : ℕ) : ℂ))+1/2) = (((n+1 : ℕ) : ℂ)^2-1)/2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (source_shape_beta_argument hn he)
    push_cast at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine ⟨?_, ?_, shapePeriod_ne_zero hn hexp hQ hd⟩
  · simpa [neg_mul, sub_eq_add_neg] using
      shapePeriod_boundary_integrable hn hexp hQ hd (δ := 0) (le_refl 0)
  · have h := shapePeriod_eq_beta hn hexp hQ hd
    rw [← ha]
    simpa only [neg_add, sub_eq_add_neg] using h

/-- Nonzero displayed leading coefficient for every source even particle order.
The identification with the physical derivative asymptotic is not part of this lemma. -/
theorem localLeadingCoefficient_ne_zero (a : OrderedChartData) {n : ℕ}
    (hn : 1 ≤ n) (he : Even (n+1)) :
    localLeadingCoefficient a n ((n+1)^2/2-1) ≠ 0 := by
  apply localLeadingCoefficient_ne_zero_of_period
  exact shapePeriod_ne_zero hn (source_shape_radial_exponent hn he)
    (a.Q_pos (by omega)) a.d_pos

end
end IsingBulk.First
