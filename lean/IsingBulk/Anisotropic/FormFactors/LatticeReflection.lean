import IsingBulk.Anisotropic.FormFactors.AngularContour
import IsingBulk.HT.Contour.PhysicalLatticeReflection

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

theorem gamma_neg (B C q : ℝ) : gamma B C (-q) = gamma B C q := by
  simp only [gamma,Real.cos_neg]

theorem rootProduct_neg {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) :
    rootProduct B C (fun i => -q i) = rootProduct B C q := by
  simp only [rootProduct,root,gamma_neg]

theorem pairProduct_neg {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) :
    pairProduct B C (fun i => -q i) = pairProduct B C q := by
  have hd (a b : ℝ) : (-a-(-b))/2 = -((a-b)/2) := by ring
  simp only [pairProduct,gamma_neg,hd,Real.sin_neg,neg_div,neg_sq]

theorem angularWeight_neg {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) :
    angularWeight B C (fun i => -q i) = angularWeight B C q := by
  simp only [angularWeight,gamma_neg,pairProduct_neg]

theorem lattice_integrand_source {N : ℕ} {B C : ℝ} (hB : 0 < B) (hgap : 1 < C-B)
    (v : ℤ × ℤ) (q : Fin N → ℝ) :
    (angularWeight B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
      Complex.exp (Complex.I*(v.2:ℂ)*(∑ i,(q i:ℂ))) =
    ((Real.sqrt B)^N:ℝ)*coordinateProduct (fun i => limitingAngle (q i))*
      canceledLatticeDensity B C 1 (fun i => limitingAngle (q i)) (v.1,0)*
        (coordinateProduct (fun i => limitingAngle (q i)))^v.2 := by
  have hh := scaled_canceledLatticeDensity_unit (S := 1) hB hgap (by norm_num) q (v.1,0)
  norm_num at hh
  push_cast
  rw [hh,physical_angle_coordinateProduct_zpow]

theorem lattice_integrand_periodic (N : ℕ) {B C : ℝ} (hB : 0 < B) (hgap : 1 < C-B)
    (v : ℤ × ℤ) : CoordinatePeriodic N (fun q =>
      (angularWeight B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
        Complex.exp (Complex.I*(v.2:ℂ)*(∑ i,(q i:ℂ)))) := by
  intro phi q
  have he : (fun i => limitingAngle (Function.update phi q (phi q+2*Real.pi) i)) =
      (fun i => limitingAngle (phi i)) := by
    rw [← physical_angleTuple_one,← physical_angleTuple_one]
    exact angleTuple_update_period 1 phi q
  dsimp only
  rw [lattice_integrand_source hB hgap,lattice_integrand_source hB hgap,he]

theorem latticeCoefficient_horizontal_reflection (N : ℕ) {B C : ℝ}
    (hB : 0 < B) (hgap : 1 < C-B) (v : ℤ × ℤ) :
    latticeCoefficient N B C (v.1,-v.2) = latticeCoefficient N B C v := by
  have hpoint (q : Fin N → ℝ) :
      (angularWeight B C (fun i => -q i)*(rootProduct B C (fun i => -q i))^v.1.natAbs:ℝ)*
        Complex.exp (Complex.I*(v.2:ℂ)*(∑ i,((-q i:ℝ):ℂ))) =
      (angularWeight B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
        Complex.exp (Complex.I*((-v.2:ℤ):ℂ)*(∑ i,(q i:ℂ))) := by
    rw [angularWeight_neg,rootProduct_neg]
    congr 1
    congr 1
    simp only [Complex.ofReal_neg,Finset.sum_neg_distrib,Int.cast_neg]
    ring
  have hh := physical_multiAngleIntegral_neg N _ (lattice_integrand_periodic N hB hgap v)
  simp_rw [hpoint] at hh
  unfold latticeCoefficient
  rw [hh]

theorem latticeCoefficient_natAbs (N : ℕ) {B C : ℝ}
    (hB : 0 < B) (hgap : 1 < C-B) (v : ℤ × ℤ) :
    latticeCoefficient N B C (v.1,(v.2.natAbs:ℤ)) = latticeCoefficient N B C v := by
  rcases le_total 0 v.2 with hv | hv
  · rw [Int.natCast_natAbs,abs_of_nonneg hv]
  · rw [Int.natCast_natAbs,abs_of_nonpos hv]
    exact latticeCoefficient_horizontal_reflection N hB hgap v

/-- The literal angular coefficient at every lattice site, not only a quadrant. -/
theorem latticeCoefficient_eq_unit_contour (N : ℕ) {B C S : ℝ} (hB : 0 < B)
    (hgap : 1 < C-B) (hS : S ≠ 0) (v : ℤ × ℤ) :
    latticeCoefficient N B C v = ((S*Real.sqrt B)^N:ℝ)*(N.factorial:ℂ)⁻¹ *
      multiCircleIntegral 1 N (fun y => canceledLatticeDensity B C (S:ℂ) y v) := by
  rw [← latticeCoefficient_natAbs N hB hgap v]
  exact latticeCoefficient_natAbs_eq_unit_contour N hB hgap hS v
end
end IsingBulk.Anisotropic.FormFactors
