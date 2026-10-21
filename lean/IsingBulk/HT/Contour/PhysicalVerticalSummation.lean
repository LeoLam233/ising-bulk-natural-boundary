import IsingBulk.HT.Contour.PhysicalAngularRegularity
import IsingBulk.HT.Contour.PhysicalLatticeSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The full vertical lattice sum on the actual zero-total-angle slice

The geometric series is dominated before it is interchanged with the coupled
angular integral. The endpoint is the literal published N-1-angle coefficient,
including the physical (1+Z)/(1-Z) multiplier and the unchanged factorial.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.HT.Final Set MeasureTheory
open scoped BigOperators

/-- The zero-total-angle slice at a fixed nonnegative vertical displacement. -/
def physicalConstrainedVerticalCoefficient (n : ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun phi =>
      let psi := physicalDependentAngles n phi
      ((physicalAngularWeight t psi*(physicalZ t psi)^m:ℝ):ℂ))

/-- Absolute vertical summability and the exact angular coefficient. Every
term retains all n+1 particle coordinates and the dependent last angle. -/
theorem physicalConstrainedVerticalCoefficient_summable_eq_angular
    (n : ℕ) {t : ℝ} (ht : 1 < t) :
    Summable (fun m : ℤ => ‖physicalConstrainedVerticalCoefficient n t m.natAbs‖) ∧
      (∑' m : ℤ, physicalConstrainedVerticalCoefficient n t m.natAbs) =
        physicalAngularCoefficient n t := by
  let S := angleBox n
  let K : ℂ := ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n
  let A : (Fin n → ℝ) → ℂ := fun phi =>
    (physicalAngularWeight t (physicalDependentAngles n phi):ℂ)
  let Z : (Fin n → ℝ) → ℂ := fun phi =>
    (physicalZ t (physicalDependentAngles n phi):ℂ)
  let rho : ℝ := (physicalRoot t 0)^(n+1)
  let F : ℤ → (Fin n → ℝ) → ℂ := fun m phi => A phi*(Z phi)^m.natAbs
  have hA : Continuous A := Complex.continuous_ofReal.comp
    ((physicalAngularWeight_continuous (n+1) ht).comp
      (physicalDependentAngles_continuous n))
  have hZc : Continuous Z := Complex.continuous_ofReal.comp
    ((physicalZ_continuous (n+1) ht).comp
      (physicalDependentAngles_continuous n))
  have hrho : 0 ≤ rho := pow_nonneg (physicalRoot_bounds ht 0).1.le _
  have hrho1 : rho < 1 :=
    pow_lt_one₀ (physicalRoot_bounds ht 0).1.le (physicalRoot_bounds ht 0).2 (by omega)
  have hZ (phi : Fin n → ℝ) : ‖Z phi‖ ≤ rho := by
    change ‖(physicalZ t (physicalDependentAngles n phi):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (physicalZ_pos ht (physicalDependentAngles n phi))]
    exact physicalZ_le_zero_pow ht (physicalDependentAngles n phi)
  have hZ1 (phi : Fin n → ℝ) : ‖Z phi‖ < 1 := (hZ phi).trans_lt hrho1
  have hgap (phi : Fin n → ℝ) : 1-Z phi ≠ 0 := by
    intro he
    have hz : Z phi=1 := (sub_eq_zero.mp he).symm
    have hh := hZ1 phi
    rw [hz,norm_one] at hh
    exact lt_irrefl (1:ℝ) hh
  have hAi : IntegrableOn A S :=
    hA.continuousOn.integrableOn_compact isCompact_Icc
  have hFc (m : ℤ) : Continuous (F m) := hA.mul (hZc.pow m.natAbs)
  have hi (m : ℤ) : IntegrableOn (F m) S :=
    (hFc m).continuousOn.integrableOn_compact isCompact_Icc
  have hbound (m : ℤ) :
      (∫ phi in S, ‖F m phi‖) ≤ (∫ phi in S, ‖A phi‖)*rho^m.natAbs := by
    rw [← integral_mul_const]
    apply integral_mono (hi m).norm (hAi.norm.mul_const _)
    intro phi
    simp only [F,norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg (Z phi)) (hZ phi) _) (norm_nonneg (A phi))
  have hsI : Summable (fun m : ℤ => ∫ phi in S, ‖F m phi‖) :=
    ((physical_real_twoSided_geometric_summable hrho hrho1).mul_left
      (∫ phi in S, ‖A phi‖)).of_nonneg_of_le
        (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have hsNorm : Summable (fun m : ℤ => ‖∫ phi in S, F m phi‖) :=
    hsI.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
  have hbox (m : ℤ) : physicalConstrainedVerticalCoefficient n t m.natAbs =
      K*(∫ phi in S,F m phi) := by
    have hc : Continuous (fun phi : Fin n → ℝ =>
        ((physicalAngularWeight t (physicalDependentAngles n phi)*
          (physicalZ t (physicalDependentAngles n phi))^m.natAbs:ℝ):ℂ)) := by
      simpa only [F,A,Z,Complex.ofReal_mul,Complex.ofReal_pow] using hFc m
    unfold physicalConstrainedVerticalCoefficient
    rw [multiAngleIntegral_eq_box n _ hc]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow]
    rfl
  have hKernel : Continuous (fun phi => A phi*((1+Z phi)/(1-Z phi))) :=
    hA.mul ((continuous_const.add hZc).div (continuous_const.sub hZc) hgap)
  have hangular : physicalAngularCoefficient n t =
      K*(∫ phi in S,A phi*((1+Z phi)/(1-Z phi))) := by
    have hc : Continuous (fun phi : Fin n → ℝ =>
        ((physicalAngularWeight t (physicalDependentAngles n phi) *
          ((1+physicalZ t (physicalDependentAngles n phi)) /
            (1-physicalZ t (physicalDependentAngles n phi))):ℝ):ℂ)) := by
      simpa only [A,Z,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add,
        Complex.ofReal_sub,Complex.ofReal_one] using hKernel
    unfold physicalAngularCoefficient
    rw [multiAngleIntegral_eq_box n _ hc]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_one]
    rfl
  constructor
  · simpa only [hbox,norm_mul] using hsNorm.mul_left ‖K‖
  · calc
      (∑' m : ℤ,physicalConstrainedVerticalCoefficient n t m.natAbs) =
          K*(∑' m : ℤ,∫ phi in S,F m phi) := by
        simp_rw [hbox]
        rw [tsum_mul_left]
      _ = K*(∫ phi in S,∑' m : ℤ,F m phi) := by
        rw [integral_tsum_of_summable_integral_norm hi hsI]
      _ = K*(∫ phi in S,A phi*((1+Z phi)/(1-Z phi))) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro phi _
        simp only [F,tsum_mul_left]
        rw [vertical_displacement_geometric_sum (hZ1 phi)]
      _ = physicalAngularCoefficient n t := hangular.symm

end
end IsingBulk.HT.Contour
