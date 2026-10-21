import IsingBulk.First.SymmetryIntegral
import IsingBulk.First.FormFactorNormalization

/-! Actual onsite parity for all N. Only the onsite coefficient has this
simple parity; no such evenness is imposed on the full HT observable. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem onsiteDensity_neg_all {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    onsiteDensity (-s) (fun i => -x i) (fun i => -y i) =
      (-1:ℂ)^N*onsiteDensity s x y := by
  have hprod (z : Fin N → ℂ) : coordinateProduct (fun i => -z i) =
      (-1:ℂ)^N*coordinateProduct z := by
    simp [coordinateProduct,Finset.prod_neg]
  have hsign : (-1:ℂ)^N*(-1:ℂ)^N = 1 := by
    rw [← mul_pow]; norm_num
  have hxy : coordinateProduct (fun i => -x i)*coordinateProduct (fun i => -y i) =
      coordinateProduct x*coordinateProduct y := by
    rw [hprod,hprod,mul_mul_mul_comm,hsign,one_mul]
  have hcommon : commonDensity (-s) (fun i => -x i) (fun i => -y i) =
      (-1:ℂ)^N*commonDensity s x y := by
    unfold commonDensity
    rw [doublePairProduct_neg]
    simp_rw [dispersion_neg,inv_neg]
    rw [Finset.prod_neg]
    simp only [Finset.card_univ,Fintype.card_fin]
    ring
  unfold onsiteDensity
  rw [hxy,hcommon]
  ring

/-- The two N-dimensional contour orientation factors cancel, even for odd N. -/
theorem doubleCircleIntegral_neg (N : ℕ) (r : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun y => multiCircleIntegral r N
      (fun x => f (fun i => -x i) (fun i => -y i))) =
    multiCircleIntegral r N (fun y => multiCircleIntegral r N (fun x => f x y)) := by
  have hsign : (-1:ℂ)^N*(-1:ℂ)^N = 1 := by rw [← mul_pow]; norm_num
  have hinner (y : Fin N → ℂ) : multiCircleIntegral r N
      (fun x => f (fun i => -x i) (fun i => -y i)) =
      (-1:ℂ)^N*multiCircleIntegral r N (fun x => f x (fun i => -y i)) :=
    multiCircleIntegral_neg r N (fun x => f x (fun i => -y i))
  simp_rw [hinner]
  rw [multiCircleIntegral_const_mul,multiCircleIntegral_neg r N
    (fun y => multiCircleIntegral r N (fun x => f x y)),← mul_assoc,hsign,one_mul]

theorem onsiteFormFactor_neg (N : ℕ) (r : ℝ) (s : ℂ) :
    onsiteFormFactor N r (-s) = (-1:ℂ)^N*onsiteFormFactor N r s := by
  unfold onsiteFormFactor
  rw [← doubleCircleIntegral_neg N r (onsiteDensity (-s))]
  simp_rw [onsiteDensity_neg_all,multiCircleIntegral_const_mul]
  ring

theorem onsiteFormFactor_neg_odd {N : ℕ} (hN : Odd N) (r : ℝ) (s : ℂ) :
    onsiteFormFactor N r (-s) = -onsiteFormFactor N r s := by
  rw [onsiteFormFactor_neg,hN.neg_one_pow,neg_one_mul]

theorem onsiteDensity_conjugate {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    onsiteDensity (star s) (fun i => star (x i)) (fun i => star (y i)) =
      star (onsiteDensity s x y) := by
  simp [onsiteDensity,commonDensity,coordinateProduct,pairProduct,pairKernel,dispersion,sourceS]

theorem onsiteFormFactor_conjugate (N : ℕ) (r : ℝ) (s : ℂ) :
    onsiteFormFactor N r (star s) = star (onsiteFormFactor N r s) := by
  unfold onsiteFormFactor
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
  simpa only [star_star] using onsiteDensity_conjugate s
    (fun i => star (x i)) (fun i => star (y i))

end
end IsingBulk.HT.Final
