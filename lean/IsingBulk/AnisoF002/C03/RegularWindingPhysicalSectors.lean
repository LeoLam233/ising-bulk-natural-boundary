import IsingBulk.AnisoF002.C03.RegularWindingPhysicalMeasurable
import IsingBulk.AnisoF002.C03.RegularWindingSectorIntegrability

/-!
# Literal complete physical winding-sector coefficients

These definitions retain the actual moving phase pole and full residue,
with the exact shared cutoff and independent-coordinate measure.
The Taylor coefficient has the minus sign from expanding 1/(t-P).
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

def physicalWindingSectorKernel {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (k : ℕ) (w : ℤ)
    (v : Angular.constrainedPlane n) : ℂ :=
  if ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ s then
    d.actualResidue (centeredWindingAngles w v) /
      d.pole (centeredWindingAngles w v) ^ k else 0

def physicalWindingSectorCoefficient {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (j : ℕ) (w : ℤ) : ℂ :=
  -(∫ v, physicalWindingSectorKernel d (j + 1) w v ∂Angular.independentMeasure n)

end
end IsingBulk.AnisoF002.NegativeHT
