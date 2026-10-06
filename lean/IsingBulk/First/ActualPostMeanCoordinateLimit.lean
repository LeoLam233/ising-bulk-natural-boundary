import IsingBulk.First.ActualPostMeanShapeLimit
import IsingBulk.First.ActualLeadingCoordinateLimit
import IsingBulk.First.ShapePeriodTheorem

/-! Source-coordinate asymptotic of the complete actual post-mean derivative,
with a proved nonzero leading coefficient and the exact source order k. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Filter
open scoped Topology

def localizedPostMeanDerivativeIntegral {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (chi : ShapeSpace n → ℂ) (epsilon : ℝ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (deriv^[k] (fun s => postMeanDensity s a.alpha t/((n+1).factorial:ℂ)))
      (radialParameter a.theta epsilon)

theorem actual_postMean_coordinate_sqrt_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • localizedPostMeanDerivativeIntegral a k chi epsilon)
        (𝓝[>] 0) (𝓝 (localLeadingCoefficient a n k)) := by
  obtain ⟨R,hR,h⟩ := actual_postMean_shape_sqrt_limit hn hk hdegree a he ha hb
  refine ⟨R,hR,?_⟩
  intro chi hchi hchi0 hchib hchis
  have ht := (h chi hchi hchi0 hchib hchis).const_smul (Real.sqrt (n+1))⁻¹
  convert ht using 1
  · funext epsilon
    have hi := integral_shapeExtend n (fun x => chi x*intrinsicPostMeanDerivative a k epsilon x)
    have hid : localizedPostMeanDerivativeIntegral a k chi epsilon =
        (Real.sqrt (n+1))⁻¹ • ∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a k epsilon x := by
      simpa only [localizedPostMeanDerivativeIntegral, intrinsicPostMeanDerivative,
        intrinsicShapeCoordinates_shapeCoordinateEquiv] using hi
    rw [hid, smul_comm]
  · congr 1
    rw [localLeadingCoefficient, shapePeriod_eq_intrinsic]
    simp only [Complex.real_smul, ofReal_mul, ofReal_ofNat]
    ring

/-- The complete actual post-mean shape integral has the manuscript's
nonzero ε⁻¹ᐟ² term at k=N²/2−1. This endpoint concerns the post-mean piece;
it does not assert any complement, contour-side, or global FIRST remainder. -/
theorem actual_postMean_source_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    let k := (n+1)^2/2-1
    localLeadingCoefficient a n k ≠ 0 ∧
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => localizedPostMeanDerivativeIntegral a k chi epsilon-
          ((Real.sqrt epsilon:ℂ)⁻¹)*localLeadingCoefficient a n k)
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
  dsimp only
  have hdegree := source_shape_radial_exponent hn he
  have hk : 1 ≤ (n+1)^2/2-1 := by
    have hp : 2 ≤ (n+1)*n := by
      have h := Nat.mul_le_mul (show 2 ≤ n+1 by omega) hn
      simpa using h
    omega
  refine ⟨localLeadingCoefficient_ne_zero a hn he,?_⟩
  obtain ⟨R,hR,h⟩ := actual_postMean_coordinate_sqrt_limit hn hk hdegree a he ha hb
  refine ⟨R,hR,?_⟩
  intro chi hchi hchi0 hchib hchis
  exact normalized_sqrt_limit_isLittleO (h chi hchi hchi0 hchib hchis)

end
end IsingBulk.First
