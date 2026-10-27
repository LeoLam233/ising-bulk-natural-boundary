import IsingBulk.Preferred22.PhysicalKernel
import IsingBulk.Preferred22.Pfaffian

/-! The all-order dispersion determinant identity specialized to the actual
interior roots and actual kernel used in the coefficient definition. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

theorem gaugeKernel_eq_dispersionMatrix {N : ℕ} (y z : Fin N → ℂ) :
    gaugeKernel y z = dispersionMatrix y z (fun i => Complex.sqrt (z i / y i)) := by
  ext i j
  simp only [gaugeKernel, dispersionMatrix, scaledPair, dispersionB]
  ring

/-- The complete determinant product on the real angular contour at every
exterior temperature, including all coincidences of angles. -/
theorem physical_determinant_product (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin (2*n) → ℝ) :
    (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ) i j)^2 := by
  rw [gaugeKernel_eq_dispersionMatrix]
  apply dispersion_determinant_product n (temperatureTrace s)
  · exact fun i => angleRoot_ne_zero (θ i)
  · exact fun i => physicalRoot_ne_zero _
  · exact fun i => angular_dispersion s (θ i)
  · exact fun i j _ => angular_pair_denominator_ne_zero hs θ i j
  · exact fun i => complex_sqrt_sq _

/-- Equation (4.4) in rational-square form, for the literal physical coefficient. -/
theorem physical_determinant_rational_product (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin (2*n) → ℝ) :
    (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        -((angleRoot (θ i)-angleRoot (θ j))^2 * angularRoots s θ i * angularRoots s θ j) /
          (angleRoot (θ i)*angleRoot (θ j)*(1-angularRoots s θ i*angularRoots s θ j)^2) := by
  rw [physical_determinant_product n hs θ]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact gaugeKernel_square _ _ i j

/-- The elementary Pfaffian identity for the actual physical angular kernel,
using a genuine signed first-row recursive Pfaffian. -/
theorem physical_pfaffian_product (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin (2*n) → ℝ) :
    PfaffianFoundation.recursivePf n
      (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)) =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ) i j := by
  rw [gaugeKernel_eq_dispersionMatrix]
  apply dispersion_pfaffian_product n (temperatureTrace s)
  · exact fun i => angleRoot_ne_zero (θ i)
  · exact fun i => physicalRoot_ne_zero _
  · exact fun i => angular_dispersion s (θ i)
  · exact fun i j _ => angular_pair_denominator_ne_zero hs θ i j
  · exact fun i => complex_sqrt_sq _

end
end IsingBulk.Preferred22
