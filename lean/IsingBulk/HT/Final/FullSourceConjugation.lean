import IsingBulk.HT.Final.RightFullSeries
import IsingBulk.HT.Final.LeftFullSeries

/-! Conjugation is established for literal full-site source contours. It is
not inferred from evenness, which does not hold for the odd HT series. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem standardDensity_conjugate {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    standardDensity (star s) (fun i => star (x i)) (fun i => star (y i)) =
      star (standardDensity s x y) := by
  simp [standardDensity,commonDensity,coordinateProduct,pairProduct,pairKernel,dispersion,sourceS]

theorem standardFormFactor_conjugate (N : ℕ) (r : ℝ) (s : ℂ) :
    standardFormFactor N r (star s) = star (standardFormFactor N r s) := by
  unfold standardFormFactor
  rw [star_mul]
  have hc : star ((N.factorial:ℂ)⁻¹) = (N.factorial:ℂ)⁻¹ := by simp
  rw [hc]
  conv_rhs => rw [mul_comm]
  congr 1
  rw [← multiCircleIntegral_conjugate]
  congr 1
  funext y
  rw [← multiCircleIntegral_conjugate]
  congr 1
  funext x
  simpa only [star_star] using standardDensity_conjugate s
    (fun i => star (x i)) (fun i => star (y i))

theorem rightFullCoefficient_conjugate (N : ℕ) (s : ℂ) :
    rightFullCoefficient N (star s) = star (rightFullCoefficient N s) := by
  simp only [rightFullCoefficient,rightOnsiteFormFactor_conjugate,
    rightFormFactor_conjugate,star_add,star_mul,star_ofNat,mul_comm]

theorem rightFullOddSeries_conjugate (s : ℂ) :
    rightFullOddSeries (star s) = star (rightFullOddSeries s) := by
  simp only [rightFullOddSeries,rightFullCoefficient_conjugate,tsum_star]

theorem fixedOddFullSeries_conjugate (r : ℝ) (s : ℂ) :
    fixedOddFullSeries r (star s) = star (fixedOddFullSeries r s) := by
  simp only [fixedOddFullSeries,oddFullCoefficient,standardFormFactor_conjugate,tsum_star]


theorem leftFormFactor_conjugate (N : ℕ) (s : ℂ) :
    leftFormFactor N (star s) = star (leftFormFactor N s) := by
  have hr : leftCanonicalRadius (star s) = leftCanonicalRadius s := by
    simp [leftCanonicalRadius]
  simp only [leftFormFactor,hr,doubleFormFactor_conjugate]

theorem leftFullCoefficient_conjugate (N : ℕ) (s : ℂ) :
    leftFullCoefficient N (star s) = star (leftFullCoefficient N s) := by
  simp only [leftFullCoefficient,leftOnsiteFormFactor_conjugate,
    leftFormFactor_conjugate,star_add,star_mul,star_ofNat,mul_comm]

end
end IsingBulk.HT.Final
