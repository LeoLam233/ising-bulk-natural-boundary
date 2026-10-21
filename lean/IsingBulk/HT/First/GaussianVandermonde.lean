import IsingBulk.HT.First.GaussianAndreief
import IsingBulk.HT.First.GaussianHermite
import IsingBulk.First.ShapeVandermonde
import Mathlib.Data.Nat.Factorial.SuperFactorial

/-! Exact unnormalized Gaussian Vandermonde integral, using the proved
Hermite pairing and finite determinant/Fubini identity. -/
namespace IsingBulk.HT.First.Gaussian
noncomputable section
open IsingBulk.First MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1200000

/-- The manuscript's pair order is opposite to mathlib's determinant
order.  Their squares agree also on all collision sets. -/
theorem firstVandermonde_sq_eq_det (n : ℕ) (x : Fin n → ℝ) :
    firstVandermonde x ^ 2 = (Matrix.vandermonde x).det ^ 2 := by
  classical
  have hIoi (i : Fin n) : Finset.Ioi i = Finset.univ.filter (fun j => i<j) := by
    ext j
    simp
  rw [firstVandermonde,Matrix.det_vandermonde]
  simp only [← Finset.prod_pow,firstStrictPairs,Finset.prod_filter,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [hIoi,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i<j
  · simp only [hij,ite_true]
    ring
  · simp only [hij,ite_false,one_pow]

/-- Actual ambient numerator and Gaussian, with Lebesgue volume. -/
def ambientGaussianVandermonde (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ i, x i^2)/2) * firstVandermonde x^2

theorem gaussianWeight_product (n : ℕ) (x : Fin n → ℝ) :
    (∏ i, gaussianWeight (x i)) = Real.exp (-(∑ i, x i^2)/2) := by
  unfold gaussianWeight
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib,Finset.sum_div,neg_div]

theorem ambientGaussianVandermonde_eq_det (n : ℕ) (x : Fin n → ℝ) :
    ambientGaussianVandermonde n x =
      (Matrix.vandermonde x).det^2 * ∏ i, gaussianWeight (x i) := by
  rw [ambientGaussianVandermonde,firstVandermonde_sq_eq_det,gaussianWeight_product,mul_comm]

/-- Absolute integrability is obtained from the actual Hermite products;
it is available independently of the scalar Gaussian evaluation. -/
theorem ambient_gaussian_vandermonde_integrable (n : ℕ) :
    Integrable (ambientGaussianVandermonde n) := by
  have hh := weighted_monic_vandermonde_integrable n (fun i => realHermite i.val)
    gaussianWeight (fun i => realHermite_natDegree i.val) (fun i => realHermite_monic i.val)
    (fun i j => hermite_gaussian_integrable i.val j.val)
  apply hh.congr
  filter_upwards [] with x
  exact (ambientGaussianVandermonde_eq_det n x).symm

/-- Literal ambient polynomial-Gaussian integrability, without a definition
wrapper, for use in the mean/shape change of variables. -/
theorem ambient_gaussian_firstVandermonde_integrable (n : ℕ) :
    Integrable (fun x : Fin n → ℝ =>
      Real.exp (-(∑ i, x i^2)/2) * firstVandermonde x^2) :=
  ambient_gaussian_vandermonde_integrable n

/-- The full factorial normalization before interval-product conversion. -/
theorem ambient_gaussian_vandermonde_integral_fin (n : ℕ) :
    (∫ x : Fin n → ℝ, ambientGaussianVandermonde n x) =
      (n.factorial:ℝ) * Real.sqrt (2*Real.pi)^n *
        ∏ i : Fin n, (i.val.factorial:ℝ) := by
  have hh := weighted_monic_vandermonde_square n (fun i => realHermite i.val)
    gaussianWeight (fun i => Real.sqrt (2*Real.pi)*(i.val.factorial:ℝ))
    (fun i => realHermite_natDegree i.val) (fun i => realHermite_monic i.val)
    (fun i j => hermite_gaussian_integrable i.val j.val) (by
      intro i j
      simpa only [Fin.val_inj] using hermite_gaussian_inner i.val j.val)
  simp_rw [ambientGaussianVandermonde_eq_det]
  rw [hh,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

/-- Exactly the manuscript's all-particle Gaussian constant. -/
theorem ambient_gaussian_vandermonde_integral (n : ℕ) :
    (∫ x : Fin n → ℝ, ambientGaussianVandermonde n x) =
      Real.sqrt (2*Real.pi)^n * ∏ m ∈ Finset.Icc 1 n, (m.factorial:ℝ) := by
  rw [ambient_gaussian_vandermonde_integral_fin]
  have hfac : (n.factorial:ℝ) * (∏ i : Fin n, (i.val.factorial:ℝ)) =
      ∏ m ∈ Finset.Icc 1 n, (m.factorial:ℝ) := by
    have hprod : (∏ i : Fin n, (i.val.factorial:ℝ)) =
        ∏ m ∈ Finset.range n, (m.factorial:ℝ) :=
      Fin.prod_univ_eq_prod_range (fun m : ℕ => (m.factorial:ℝ)) n
    rw [hprod]
    have hnat : n.factorial * (∏ m ∈ Finset.range n, m.factorial) =
        ∏ m ∈ Finset.Icc 1 n, m.factorial := by
      rw [Nat.prod_Icc_factorial,← Nat.prod_range_succ_factorial,Finset.prod_range_succ]
      ring
    exact_mod_cast hnat
  calc
    _ = Real.sqrt (2*Real.pi)^n *
        ((n.factorial:ℝ) * ∏ i : Fin n, (i.val.factorial:ℝ)) := by ring
    _ = _ := by rw [hfac]

end
end IsingBulk.HT.First.Gaussian
