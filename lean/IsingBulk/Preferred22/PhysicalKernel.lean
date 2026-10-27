import IsingBulk.Preferred22.Physical
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Group.Integral

/-! Algebraic branch and gauge facts for the literal physical angular kernel.
The determinant normalization removes all square-root sign choices. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set

theorem physicalRoot_neg {W : ℂ} (hW : OffRealSegment W) :
    physicalRoot (-W) = -physicalRoot W := by
  have hn : OffRealSegment (-W) := by simpa [OffRealSegment] using hW
  have ht : -physicalRoot W + (-physicalRoot W)⁻¹ = 2 * (-W) := by
    rw [inv_neg]
    linear_combination -(physicalRoot_trace W)
  exact root_unique_in_disk (physicalRoot_trace (-W)) ht
    (physicalRoot_ne_zero (-W)) (neg_ne_zero.mpr (physicalRoot_ne_zero W))
    (physicalRoot_inside hn) (by simpa using physicalRoot_inside hW)

theorem physicalRoot_conj {W : ℂ} (hW : OffRealSegment W) :
    physicalRoot (star W) = star (physicalRoot W) := by
  have hc : OffRealSegment (star W) := by simpa [OffRealSegment] using hW
  have ht : star (physicalRoot W) + (star (physicalRoot W))⁻¹ = 2 * star W := by
    have h := congrArg (star : ℂ → ℂ) (physicalRoot_trace W)
    simpa using h
  exact root_unique_in_disk (physicalRoot_trace (star W)) ht
    (physicalRoot_ne_zero (star W)) (by simpa using physicalRoot_ne_zero W)
    (physicalRoot_inside hc) (by simpa using physicalRoot_inside hW)

theorem angleRoot_ne_zero (θ : ℝ) : angleRoot θ ≠ 0 := Complex.exp_ne_zero _

theorem angleRoot_norm (θ : ℝ) : ‖angleRoot θ‖ = 1 := by
  simp [angleRoot, Complex.norm_exp]

theorem angleRoot_trace (θ : ℝ) : angleRoot θ + (angleRoot θ)⁻¹ = 2 * (Real.cos θ : ℂ) := by
  unfold angleRoot
  rw [← Complex.exp_neg]
  simpa only [mul_comm Complex.I (θ : ℂ), neg_mul,
    Complex.ofReal_cos] using (Complex.two_cos (θ : ℂ)).symm

theorem angleRoot_neg (θ : ℝ) : angleRoot (-θ) = star (angleRoot θ) := by
  simpa [angleRoot] using Complex.exp_conj (Complex.I * (θ : ℂ))

theorem angleRoot_add_pi (θ : ℝ) : angleRoot (θ + Real.pi) = -angleRoot θ := by
  unfold angleRoot
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have h : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    simpa [mul_comm] using Complex.exp_pi_mul_I
  rw [h]
  ring

theorem angular_dispersion (s : ℂ) (θ : ℝ) :
    angleRoot θ + (angleRoot θ)⁻¹ + physicalRoot (angularW s θ) +
      (physicalRoot (angularW s θ))⁻¹ = 2 * temperatureTrace s := by
  rw [angleRoot_trace]
  have h := physicalRoot_trace (angularW s θ)
  dsimp [angularW]
  dsimp [angularW] at h
  linear_combination h

theorem angular_pair_denominator_ne_zero {N : ℕ} {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin N → ℝ) (i j : Fin N) : 1 - angularRoots s θ i * angularRoots s θ j ≠ 0 := by
  have hi := angularRoots_inside hs θ i
  have hj := angularRoots_inside hs θ j
  intro h
  have hp : angularRoots s θ i * angularRoots s θ j = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖angularRoots s θ i * angularRoots s θ j‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ ‖angularRoots s θ i‖ * 1 := mul_le_mul_of_nonneg_left hj.le (norm_nonneg _)
      _ < 1 := by simpa [angularRoots] using hi
  rw [hp, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

def rationalKernel {N : ℕ} (y z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (y i - y j) / (1 - z i * z j)

theorem gaugeKernel_det_normalization {N : ℕ} (y z : Fin N → ℂ) :
    (gaugeKernel y z).det = (-Complex.I)^N * (∏ i, z i / y i) * (rationalKernel y z).det := by
  let r : Fin N → ℂ := fun i => Complex.sqrt (z i / y i)
  have hmatrix : gaugeKernel y z =
      Matrix.diagonal (fun i => -Complex.I * r i) * rationalKernel y z * Matrix.diagonal r := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, gaugeKernel, rationalKernel, r]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod : (∏ i, r i) * (∏ i, r i) = ∏ i, z i / y i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact (pow_two (r i)).symm.trans (complex_sqrt_sq (z i / y i))
  calc
    _ = (-Complex.I)^N * ((∏ i, r i) * (∏ i, r i)) * (rationalKernel y z).det := by ring
    _ = _ := by rw [hprod]

theorem gaugeKernel_square {N : ℕ} (y z : Fin N → ℂ) (i j : Fin N) :
    (gaugeKernel y z i j)^2 =
      -((y i-y j)^2*z i*z j)/(y i*y j*(1-z i*z j)^2) := by
  unfold gaugeKernel
  rw [div_pow]
  repeat rw [mul_pow]
  rw [complex_sqrt_sq, complex_sqrt_sq]
  norm_num [Complex.I_sq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gaugeKernel_det_odd {N : ℕ} (hN : Odd N) (y z : Fin N → ℂ) :
    (gaugeKernel y z).det = 0 := by
  have hT : (gaugeKernel y z).transpose = -gaugeKernel y z := by
    ext i j
    exact gaugeKernel_skew y z i j
  have h := congrArg Matrix.det hT
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, hN.neg_one_pow] at h
  linear_combination (1/2 : ℂ) * h

theorem fullAngularDensity_odd {N : ℕ} (hN : Odd N) (s : ℂ) (θ : Fin N → ℝ) :
    fullAngularDensity s θ = 0 := by
  simp [fullAngularDensity, gaugeKernel_det_odd hN]

theorem coefficient_odd {N : ℕ} (hN : Odd N) (s : ℂ) : coefficient N s = 0 := by
  cases N with
  | zero => rfl
  | succ n => simp [coefficient, fullAngularDensity_odd hN]

theorem siteCoefficient_odd {N : ℕ} (hN : Odd N) (a b : ℤ) (s : ℂ) :
    siteCoefficient N a b s = 0 := by
  simp [siteCoefficient, gaugeKernel_det_odd hN]

end
end IsingBulk.Preferred22
