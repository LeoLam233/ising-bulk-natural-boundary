import IsingBulk.HT.First.OddActualPostMeanShapeLimit
import IsingBulk.First.ActualLeadingCoordinateLimit
import IsingBulk.First.ActualPostMeanCoordinateLimit
import IsingBulk.HT.First.OddShapePeriod

/-! Source-coordinate asymptotic of the complete actual post-mean derivative,
with a proved nonzero leading coefficient and the exact source order k. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Filter IsingBulk.First
open scoped Topology

theorem actual_postMean_coordinate_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : OrderedChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • localizedPostMeanDerivativeIntegral a k chi epsilon)
        (𝓝[>] 0) (𝓝 (-I*localLeadingCoefficient a n k)) := by
  obtain ⟨R,hR,h⟩ := actual_postMean_shape_epsilon_limit hn hk hdegree a ho ha hb
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

end
end IsingBulk.HT.First
