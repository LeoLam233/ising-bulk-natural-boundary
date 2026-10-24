import IsingBulk.Anisotropic.Final.IsotropicCoefficients
import IsingBulk.Tail.ExteriorSeries
import IsingBulk.HT.Contour.PhysicalLatticeResidue

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors IsingBulk.HT.Contour IsingBulk.First IsingBulk.Tail

theorem physicalFullLatticeCoefficient_zero_eq_onsite (N : ℕ) {t r : ℝ}
    (ht : 1<t) (hr : 0<r) (hr1 : r<1) (hm : 1+r⁻¹<(sourceS (t:ℂ)).re) :
    physicalFullLatticeCoefficient N t (0,0) = onsiteFormFactor N r (t:ℂ) := by
  unfold physicalFullLatticeCoefficient
  simp only [Int.natAbs_zero]
  simpa [onsiteFormFactor] using physicalLatticeCoefficient_eq_double_contour N 0 0 ht hr hr1 hm

theorem physicalAngularCoefficient_eq_onsite_add_right (n : ℕ) {t : ℝ} (ht : 1<t) :
    physicalAngularCoefficient n t = physicalFullLatticeCoefficient (n+1) t (0,0) +
      2*rightFormFactor (n+1) (t:ℂ) := by
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible
    (IsingBulk.HT.Final.physical_real_trace_gt_two ht)
  rw [physicalAngularCoefficient_eq_standardFormFactor n ht hr hr1 hm,
    standardFormFactor_eq_onsite_add_double (n+1) (by omega) _ _ _
      (rightRoot_admissible hr hr1 hm),
    physicalFullLatticeCoefficient_zero_eq_onsite _ ht hr hr1 hm,
    rightFormFactor_eq_fixed_radius (n+1) (by omega) hr hr1 hm]

theorem isotropic_low_real_parameters {x : ℝ} (hx : criticalPoint 1<x) :
    0<x ∧ 1<Real.sinh x ∧ realProduct 1 x≠1 := by
  have hx0 := lt_trans (criticalPoint_pos (by norm_num : (0:ℝ)<1)) hx
  have hs := Real.sinh_pos_iff.mpr hx0
  have hp := (criticalPoint_lt_iff_product_gt_one (by norm_num : (0:ℝ)<1) hx0.le).mp hx
  simp only [one_mul] at hp
  refine ⟨hx0,?_,?_⟩
  · nlinarith
  · rw [realProduct_one]
    nlinarith

theorem isotropic_low_weighted_term (n : ℕ) {x : ℝ} (hx : criticalPoint 1<x) :
    spectralProduct 1 (x:ℂ)^(n+1)*unscaledFullCoefficient (2*n+2) 1 (x:ℂ) =
      physicalFullLatticeCoefficient (2*n+2) (Real.sinh x) (0,0) +
      2*exteriorEvenTerm n (Real.sinh x:ℂ) := by
  obtain ⟨hx0,hs,hp⟩ := isotropic_low_real_parameters hx
  have he := isotropic_scaled_coefficient_eq_angular (2*n+1) hx0 hs rfl hp
  rw [physicalAngularCoefficient_eq_onsite_add_right (2*n+1) hs] at he
  rw [exteriorEvenTerm_eq_right n (IsingBulk.HT.Final.physical_real_trace_gt_two hs)]
  convert he using 1
  · simp only [spectralProduct,spectralS,spectralT,Complex.ofReal_one,one_mul,← Complex.ofReal_sinh]
    ring

end
end IsingBulk.Anisotropic
