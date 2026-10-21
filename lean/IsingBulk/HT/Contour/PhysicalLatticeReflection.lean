import IsingBulk.HT.Contour.PhysicalLatticeContour
import IsingBulk.First.PeriodicBoxIntegral
import IsingBulk.First.SourceAngularPeriodicity

/-!
# Horizontal reflection of the literal physical lattice coefficients

Every angle is reversed in its actual periodic integral. In particular the
horizontal lattice reflection used in quadrant counting is proved here;
it is not inferred from an even-particle susceptibility identity.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem physical_multiAngleIntegral_neg (N : ℕ) (F : (Fin N → ℝ) → ℂ)
    (hF : CoordinatePeriodic N F) :
    multiAngleIntegral N (fun phi => F (fun i => -phi i)) =
      multiAngleIntegral N F := by
  induction N with
  | zero =>
    simp only [multiAngleIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ N ih =>
    have hinner (phi : Fin N → ℝ) :
        (∫ u : ℝ in 0..2*Real.pi,
          F (fun i => -(Fin.cons u phi : Fin (N+1) → ℝ) i)) =
        ∫ u : ℝ in 0..2*Real.pi,
          F (Fin.cons u (fun i => -phi i)) := by
      have he (u : ℝ) :
          (fun i => -(Fin.cons u phi : Fin (N+1) → ℝ) i) =
            Fin.cons (-u) (fun i => -phi i) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp_rw [he]
      rw [intervalIntegral.integral_comp_neg
        (fun u : ℝ => F (Fin.cons u (fun i => -phi i)))]
      have hp := (coordinatePeriodic_cons_zero hF (fun i => -phi i)).intervalIntegral_add_eq
        (-(2*Real.pi)) 0
      simp only [neg_add_cancel,zero_add] at hp
      rw [neg_zero,hp]
    simp only [multiAngleIntegral]
    simp_rw [hinner]
    exact ih _ (coordinatePeriodic_cons_integral hF)

theorem physicalGamma_neg (t phi : ℝ) :
    physicalGamma t (-phi) = physicalGamma t phi := by
  simp only [physicalGamma,Real.cos_neg]

theorem physicalRoot_neg (t phi : ℝ) :
    physicalRoot t (-phi) = physicalRoot t phi := by
  simp only [physicalRoot,physicalGamma_neg]

theorem physicalZ_neg {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) :
    physicalZ t (fun i => -phi i) = physicalZ t phi := by
  simp only [physicalZ,physicalRoot_neg]

theorem physicalPairProduct_neg {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) :
    physicalPairProduct t (fun i => -phi i) = physicalPairProduct t phi := by
  have hdiff (a b : ℝ) : (-a-(-b))/2 = -((a-b)/2) := by ring
  simp only [physicalPairProduct,physicalGamma_neg,hdiff,Real.sin_neg,neg_div,neg_sq]

theorem physicalAngularWeight_neg {N : ℕ} (t : ℝ) (phi : Fin N → ℝ) :
    physicalAngularWeight t (fun i => -phi i) = physicalAngularWeight t phi := by
  simp only [physicalAngularWeight,physicalGamma_neg,physicalPairProduct_neg]

theorem physical_latticeAngularIntegrand_eq_source {N : ℕ} {t : ℝ} (ht : 1 < t)
    (m : ℕ) (n : ℤ) (phi : Fin N → ℝ) :
    ((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ) *
        Complex.exp (Complex.I*(n:ℂ)*(∑ i,(phi i:ℂ))) =
      coordinateProduct (fun i => limitingAngle (phi i)) *
        onsiteCanceledDensity (fun i => rightRoot (t:ℂ) (limitingAngle (phi i)))
          (fun i => limitingAngle (phi i)) *
        (coordinateProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i))))^m *
        (coordinateProduct (fun i => limitingAngle (phi i)))^n := by
  rw [physical_onsiteCanceledDensity_unit ht,physical_root_coordinateProduct ht,
    physical_angle_coordinateProduct_zpow]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]

/-- Periodicity is inherited from the genuine unit-circle source, so no
uncanceled pair denominator or half-angle sign is discarded. -/
theorem physical_latticeAngularIntegrand_periodic (N : ℕ) {t : ℝ} (ht : 1 < t)
    (m : ℕ) (n : ℤ) :
    CoordinatePeriodic N (fun phi =>
      ((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ) *
        Complex.exp (Complex.I*(n:ℂ)*(∑ i,(phi i:ℂ)))) := by
  intro phi q
  have he : (fun i => limitingAngle (Function.update phi q (phi q+2*Real.pi) i)) =
      (fun i => limitingAngle (phi i)) := by
    rw [← physical_angleTuple_one,← physical_angleTuple_one]
    exact angleTuple_update_period 1 phi q
  have he' (i : Fin N) :
      limitingAngle (Function.update phi q (phi q+2*Real.pi) i) =
        limitingAngle (phi i) := congrFun he i
  dsimp only
  rw [physical_latticeAngularIntegrand_eq_source ht,
    physical_latticeAngularIntegrand_eq_source ht]
  simp_rw [he']

theorem physicalLatticeCoefficient_horizontal_reflection (N : ℕ) {t : ℝ}
    (ht : 1 < t) (m : ℕ) (n : ℤ) :
    physicalLatticeCoefficient N t m (-n) =
      physicalLatticeCoefficient N t m n := by
  have hpoint (phi : Fin N → ℝ) :
      ((physicalAngularWeight t (fun i => -phi i)*
          (physicalZ t (fun i => -phi i))^m:ℝ):ℂ) *
          Complex.exp (Complex.I*(n:ℂ)*(∑ i,((-phi i:ℝ):ℂ))) =
      ((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ) *
          Complex.exp (Complex.I*((-n:ℤ):ℂ)*(∑ i,(phi i:ℂ))) := by
    rw [physicalAngularWeight_neg,physicalZ_neg]
    congr 1
    congr 1
    simp only [Complex.ofReal_neg,Finset.sum_neg_distrib,Int.cast_neg]
    ring
  have h := physical_multiAngleIntegral_neg N
    (fun phi => ((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ) *
      Complex.exp (Complex.I*(n:ℂ)*(∑ i,(phi i:ℂ))))
    (physical_latticeAngularIntegrand_periodic N ht m n)
  simp_rw [hpoint] at h
  unfold physicalLatticeCoefficient
  rw [h]

end
end IsingBulk.HT.Contour
