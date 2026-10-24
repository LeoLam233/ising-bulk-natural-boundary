import IsingBulk.Anisotropic.FormFactors.PhysicalLatticeSum
import IsingBulk.Anisotropic.Final.RealPrefactors
import IsingBulk.HT.Contour.PhysicalAngularIdentification
import IsingBulk.HT.Final.PhysicalLatticeSeries

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors IsingBulk.HT.Contour IsingBulk.First IsingBulk.Tail

theorem realB_one {x : ℝ} (hx : 0<x) : realB 1 x=1 := by
  simp [realB,(Real.sinh_pos_iff.mpr hx).ne']

theorem realC_one {x : ℝ} (hx : 0<x) : realC 1 x=Real.sinh x+(Real.sinh x)⁻¹ := by
  have hn := (Real.sinh_pos_iff.mpr hx).ne'
  have hh := Real.cosh_sq_sub_sinh_sq x
  unfold realC
  simp only [one_mul]
  field_simp
  nlinarith

theorem realProduct_one (x : ℝ) : realProduct 1 x=Real.sinh x^2 := by
  simp [realProduct,pow_two]

theorem sqrt_realProduct_one {x : ℝ} (hx : 0<x) : Real.sqrt (realProduct 1 x)=Real.sinh x := by
  rw [realProduct_one,Real.sqrt_sq (Real.sinh_pos_iff.mpr hx).le]

theorem isotropic_scaled_coefficient_eq_angular (n : ℕ) {x t : ℝ}
    (hx : 0<x) (ht : 1<t) (htrace : t+t⁻¹=Real.sinh x+(Real.sinh x)⁻¹)
    (hp : realProduct 1 x≠1) :
    (Real.sinh x:ℂ)^(n+1)*unscaledFullCoefficient (n+1) 1 (x:ℂ) =
      physicalAngularCoefficient n t := by
  let r := rightCanonicalRadius (t:ℂ)
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible
    (IsingBulk.HT.Final.physical_real_trace_gt_two ht)
  rw [physicalAngularCoefficient_eq_fullLattice_tsum n ht hr hr1 hm]
  have hl := (physical_lattice_summable_eq_full (n+1) (by omega) (by norm_num : (0:ℝ)<1) hx hp).2
  rw [sqrt_realProduct_one hx,Complex.ofReal_pow] at hl
  rw [← hl]
  apply tsum_congr
  intro v
  rw [realB_one hx,realC_one hx,← htrace,latticeCoefficient_isotropic]

end
end IsingBulk.Anisotropic
