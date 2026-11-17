import IsingBulk.AnisoF002.C03.IsotropicPhysicalDensity
import IsingBulk.AnisoF002.C03.IsotropicConstructedCurrent

/-!
# The actual covariance current on the physical right homotopy

The regular coordinate map, covariance field, angular velocity, and
scalar determinant are actual functions. The velocity is constructed
from the coordinate matrix and is identified with the full balanced
Jacobian formula of frozen F002. No current or smooth velocity is
postulated as a hypothesis.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualTimeDirection : ℂ × (ι → ℝ) := (1, 0)

def actualCovarianceRegularField (η τ ξ : ℝ) (i : ι) (q : ℂ × (ι → ℝ)) : ℂ :=
  rightCovarianceField q.1 (fun j => actualPhysicalCoordinate η τ ξ j q) i

def actualCovarianceAngularVelocity (η τ ξ : ℝ) (i : ι) (q : ℂ × (ι → ℝ)) : ℂ :=
  constructedAngularVelocity (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualCovarianceRegularField η τ ξ) i q

omit [DecidableEq ι] in
theorem actualPhysicalCoordinate_timePartial (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) (i : ι)
    (hq : 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im) :
    scalarPartial (actualPhysicalCoordinate η τ ξ i) actualTimeDirection q =
      -1 / Complex.sin (actualPhysicalPhase η τ ξ q i) := by
  rw [scalarPartial, actualPhysicalCoordinate_fderiv η τ ξ i q actualTimeDirection hq]
  have hz : actualBalancedJacobian η τ ξ q.2 (fun _ : ι => (0 : ℂ)) i = 0 :=
    congrFun (map_zero (actualBalancedJacobian η τ ξ q.2)) i
  simp [actualTimeDirection, actualPhysicalPhase, hz, neg_div]

omit [DecidableEq ι] in
theorem actual_inverse_slopes (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) (i : ι)
    (hU : AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q))
    (hc : Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0)
    (hD : explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0)
    (heq : explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i) :
    deriv (fun z => explicitRightInverse (q.1, z)) (actualPhysicalCoordinate η τ ξ i q) =
        Complex.sin (actualPhysicalPhase η τ ξ q i) /
          (Complex.sin (actualPhysicalPhase η τ ξ q i) -
            Complex.sin (actualHomotopyAngle η τ ξ q.2 i)) ∧
      deriv (fun z => explicitRightInverse (z, actualPhysicalCoordinate η τ ξ i q)) q.1 =
        1 / (Complex.sin (actualPhysicalPhase η τ ξ q i) -
            Complex.sin (actualHomotopyAngle η τ ξ q.2 i)) := by
  have hd := explicitRightInverse_dispersion_eventually
    (q.1, actualPhysicalCoordinate η τ ξ i q) hc
  have hv := (joint_inverse_coordinate_derivative explicitRightInverse q.1
    (actualPhysicalCoordinate η τ ξ i q) hU hd hD).deriv
  have hs := (joint_inverse_parameter_derivative explicitRightInverse q.1
    (actualPhysicalCoordinate η τ ξ i q) hU hd hD).deriv
  have heφ : actualPhysicalCoordinate η τ ξ i q - actualHomotopyAngle η τ ξ q.2 i =
      actualPhysicalPhase η τ ξ q i := by
    simp [actualPhysicalCoordinate, physicalRegularCoordinate, actualPhysicalPhase]
  rw [heq, heφ] at hv hs
  exact ⟨hv, hs⟩

omit [DecidableEq ι] in
theorem actual_inverse_chain_coefficients (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) (i : ι)
    (hq : 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q))
    (hc : Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0)
    (hD : explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0)
    (heq : explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i) :
    deriv (fun z => explicitRightInverse (q.1, z)) (actualPhysicalCoordinate η τ ξ i q) *
        actualCoordinateMultiplier η τ ξ q i = 1 ∧
      deriv (fun z => explicitRightInverse (q.1, z)) (actualPhysicalCoordinate η τ ξ i q) *
        scalarPartial (actualPhysicalCoordinate η τ ξ i) actualTimeDirection q =
        -deriv (fun z => explicitRightInverse (z, actualPhysicalCoordinate η τ ξ i q)) q.1 := by
  have hφ : Complex.sin (actualPhysicalPhase η τ ξ q i) ≠ 0 :=
    upperPhysicalPhase_sin_ne_zero _ hq
  have heφ : actualPhysicalCoordinate η τ ξ i q - actualHomotopyAngle η τ ξ q.2 i =
      actualPhysicalPhase η τ ξ q i := by
    simp [actualPhysicalCoordinate, physicalRegularCoordinate, actualPhysicalPhase]
  have hD' : Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0 := by
    simpa only [explicitRightDenominator, heq, heφ] using hD
  obtain ⟨hv, hs⟩ := actual_inverse_slopes η τ ξ q i hU hc hD heq
  rw [hv, actualCoordinateMultiplier, actualPhysicalCoordinate_timePartial η τ ξ q i hq, hs]
  constructor <;> field_simp [hD', hφ]

/-- The constructed current velocity is the frozen full-Jacobian
velocity, with no population derivative omitted. -/
theorem actualCovarianceAngularVelocity_balanced (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (hdata : ∀ i,
      AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ∧
      Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0 ∧
      explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 ∧
      explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
        actualHomotopyAngle η τ ξ q.2 i) :
    actualBalancedJacobian η τ ξ q.2 (fun i => actualCovarianceAngularVelocity η τ ξ i q) =
      fun i => -(deriv (fun z => explicitRightInverse (z, actualPhysicalCoordinate η τ ξ i q)) q.1 +
        deriv (fun z => explicitRightInverse (q.1, z)) (actualPhysicalCoordinate η τ ξ i q) *
          actualCovarianceRegularField η τ ξ i q) := by
  let χ : ι → (ℂ × (ι → ℝ)) → ℂ := actualPhysicalCoordinate η τ ξ
  let e : ι → ℂ × (ι → ℝ) := actualAngularDirection
  let V := fun i => actualCovarianceAngularVelocity η τ ξ i q
  have ht := constructedAngularVelocity_transport χ e actualTimeDirection q
    (actualCovarianceRegularField η τ ξ) hdet
  have hmat := actualPhysicalCoordinate_matrix η τ ξ q hq
  funext i
  obtain ⟨hc, ha⟩ := actual_inverse_chain_coefficients η τ ξ q i (hq i)
    (hdata i).1 (hdata i).2.1 (hdata i).2.2.1 (hdata i).2.2.2
  let u := deriv (fun z => explicitRightInverse (q.1, z)) (actualPhysicalCoordinate η τ ξ i q)
  have hentry (j : ι) : u * scalarCoordinateMatrix χ e q i j = actualBalancedMatrix η τ ξ q.2 i j := by
    rw [hmat, Matrix.diagonal_mul, ← mul_assoc, hc, one_mul]
  have hsum : u * (∑ j, scalarCoordinateMatrix χ e q i j * V j) =
      actualBalancedJacobian η τ ξ q.2 V i := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ j, actualBalancedMatrix η τ ξ q.2 i j * V j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, hentry]
      _ = _ := congrFun (LinearMap.toMatrix'_mulVec (actualBalancedJacobian η τ ξ q.2) V) i
  have hti := congrFun ht i
  change scalarPartial (χ i) actualTimeDirection q -
      (∑ j, scalarCoordinateMatrix χ e q i j * V j) = actualCovarianceRegularField η τ ξ i q at hti
  change u * scalarPartial (χ i) actualTimeDirection q = _ at ha
  change actualBalancedJacobian η τ ξ q.2 V i = _
  rw [← hsum]
  linear_combination -u * hti + ha

omit [DecidableEq ι] in
theorem actualCovarianceRegularField_differentiableAt (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) q)
    (hB : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => rightCovarianceField p.1 p.2)
      (q.1, fun i => actualPhysicalCoordinate η τ ξ i q)) (i : ι) :
    DifferentiableAt ℝ (actualCovarianceRegularField η τ ξ i) q := by
  have hχ' : DifferentiableAt ℝ (fun y => (y.1, fun j => actualPhysicalCoordinate η τ ξ j y)) q :=
    differentiableAt_fst.prodMk (differentiableAt_pi.mpr (fun j => (hχ j).differentiableAt (by norm_num)))
  exact differentiableAt_pi.mp (hB.restrictScalars.differentiableAt.comp q hχ') i

end IsingBulk.AnisoF002.Isotropic
