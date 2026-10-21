import IsingBulk.HT.Contour.PhysicalAngularPairs
import IsingBulk.HT.Contour.OnsiteDensity

/-!
# Literal physical lattice coefficients on the unit contour

This is the integral attachment of the real root, complete canceled pairs and
one-body residue identities. The two displacement indices are retained: the
vertical index is a natural power of the root product, and the horizontal
index is an integer power of the angular product. No Fourier sum, infinite
lattice sum or contour-radius deformation is assumed by these identities.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem physical_multiAngleIntegral_const_mul (N : ℕ) (a : ℂ)
    (F : (Fin N → ℝ) → ℂ) :
    multiAngleIntegral N (fun phi => a*F phi) =
      a*multiAngleIntegral N F := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [multiAngleIntegral,intervalIntegral.integral_const_mul]
    exact ih _

theorem physical_anglePoint_one (phi : ℝ) :
    anglePoint 1 phi = limitingAngle phi := by
  simp [anglePoint,circleMap,limitingAngle,mul_comm]

theorem physical_angleTuple_one {N : ℕ} (phi : Fin N → ℝ) :
    angleTuple 1 phi = (fun i => limitingAngle (phi i)) := by
  funext i
  exact physical_anglePoint_one (phi i)

/-- The normalizing measure contributes exactly one angular product. -/
theorem physical_angleProductJacobian {N : ℕ} (r : ℝ) (phi : Fin N → ℝ) :
    angleProductJacobian r phi =
      coordinateProduct (angleTuple r phi)/(2*(Real.pi:ℂ))^N := by
  simp only [angleProductJacobian,angleJacobian,Finset.prod_div_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,coordinateProduct,angleTuple]

theorem physical_root_coordinateProduct {N : ℕ} {t : ℝ} (ht : 1 < t)
    (phi : Fin N → ℝ) :
    coordinateProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i))) =
      (physicalZ t phi:ℂ) := by
  simp only [coordinateProduct,physicalZ,Complex.ofReal_prod,rightRoot_real_unit_angle ht]

/-- The integer power is the actual horizontal Fourier multiplier, also for
negative horizontal displacement. -/
theorem physical_angle_coordinateProduct_zpow {N : ℕ} (phi : Fin N → ℝ) (n : ℤ) :
    (coordinateProduct (fun i => limitingAngle (phi i)))^n =
      Complex.exp (Complex.I*(n:ℂ)*(∑ i,(phi i:ℂ))) := by
  have hprod : coordinateProduct (fun i => limitingAngle (phi i)) =
      Complex.exp ((∑ i,(phi i:ℂ))*Complex.I) := by
    simp only [coordinateProduct,limitingAngle,Finset.sum_mul,Complex.exp_sum]
  rw [hprod,← Complex.exp_int_mul]
  congr 1
  ring

/-- The full, collision-regular onsite source, not a pairwise surrogate. -/
theorem physical_onsiteCanceledDensity_unit {N : ℕ} {t : ℝ} (ht : 1 < t)
    (phi : Fin N → ℝ) :
    coordinateProduct (fun i => limitingAngle (phi i)) *
      onsiteCanceledDensity
        (fun i => rightRoot (t:ℂ) (limitingAngle (phi i)))
        (fun i => limitingAngle (phi i)) = (physicalAngularWeight t phi:ℂ) := by
  have h := physical_onsite_unit_density ht phi
  dsimp only at h
  unfold onsiteCanceledDensity
  calc
    _ = coordinateProduct (fun i => limitingAngle (phi i)) *
        (coordinateProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i))) *
          coordinateProduct (fun i => limitingAngle (phi i)))⁻¹ *
        canceledPairProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i)))
          (fun i => limitingAngle (phi i)) *
        (∏ i,residueFactor (rightRoot (t:ℂ) (limitingAngle (phi i)))) := by ring
    _ = _ := h

/-- Exact angular/contour equality for each physical lattice coefficient.
This includes its factorial, every angular normalization, all complete pairs
and both displacement multipliers. It does not assert a full lattice sum. -/
theorem physicalLatticeCoefficient_eq_unit_contour (N : ℕ) {t : ℝ} (ht : 1 < t)
    (m : ℕ) (n : ℤ) :
    physicalLatticeCoefficient N t m n =
      (N.factorial:ℂ)⁻¹ * multiCircleIntegral 1 N (fun y =>
        onsiteCanceledDensity (fun i => rightRoot (t:ℂ) (y i)) y *
          (coordinateProduct (fun i => rightRoot (t:ℂ) (y i)))^m *
          (coordinateProduct y)^n) := by
  have hpoint (phi : Fin N → ℝ) :
      angleProductJacobian 1 phi *
        (onsiteCanceledDensity (fun i => rightRoot (t:ℂ) (angleTuple 1 phi i))
            (angleTuple 1 phi) *
          (coordinateProduct (fun i => rightRoot (t:ℂ) (angleTuple 1 phi i)))^m *
          (coordinateProduct (angleTuple 1 phi))^n) =
      ((2*(Real.pi:ℂ))⁻¹)^N *
        (((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ) *
          Complex.exp (Complex.I*(n:ℂ)*(∑ i,(phi i:ℂ)))) := by
    rw [physical_angleProductJacobian,physical_angleTuple_one]
    calc
      _ = ((2*(Real.pi:ℂ))⁻¹)^N *
          (coordinateProduct (fun i => limitingAngle (phi i)) *
            onsiteCanceledDensity
              (fun i => rightRoot (t:ℂ) (limitingAngle (phi i)))
              (fun i => limitingAngle (phi i))) *
          (coordinateProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i))))^m *
          (coordinateProduct (fun i => limitingAngle (phi i)))^n := by
        simp only [div_eq_mul_inv,inv_pow]
        ring
      _ = _ := by
        rw [physical_onsiteCanceledDensity_unit ht,physical_root_coordinateProduct ht,
          physical_angle_coordinateProduct_zpow]
        simp only [Complex.ofReal_mul,Complex.ofReal_pow]
        ring
  rw [multiCircleIntegral_eq_angle]
  simp_rw [hpoint]
  rw [physical_multiAngleIntegral_const_mul]
  unfold physicalLatticeCoefficient
  ring

end
end IsingBulk.HT.Contour
