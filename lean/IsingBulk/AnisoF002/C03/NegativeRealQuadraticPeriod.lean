import IsingBulk.AnisoF002.C03.NegativeQuadraticPeriods

/-!
# Exact real quadratic periods and winding suppression

These are the same independent-plane measure and complete Vandermonde
as the physical residue sectors.  Every factorial is retained, and
scaling the positive mass by w² gives the exact higher-winding power.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

def realQuadraticWeight (d k : ℕ) (m : ℝ) (v : constrainedPlane d) : ℝ :=
  planeVandermonde v / (m + ‖v‖ ^ 2) ^ k

theorem realQuadraticWeight_nonneg (d k : ℕ) {m : ℝ} (hm : 0 ≤ m) (v : constrainedPlane d) :
    0 ≤ realQuadraticWeight d k m v :=
  div_nonneg (planeVandermonde_nonneg v) (pow_nonneg (add_nonneg hm (sq_nonneg ‖v‖)) k)

theorem quadraticPeriod_one_real (d k : ℕ) (m : ℝ) (v : constrainedPlane d) :
    quadraticPeriodIntegrand d k m 1 v = (realQuadraticWeight d k m v : ℂ) := by
  simp only [quadraticPeriodIntegrand, realQuadraticWeight, one_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add]

theorem realQuadraticWeight_integrable {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {m : ℝ} (hm : 0 < m) :
    Integrable (realQuadraticWeight d k m) (independentMeasure d) := by
  have he : α + (k - α - 1) + 1 = k := by omega
  have hi := quadraticPeriod_integer_integrable hd hα (k - α - 1) hm (by norm_num : 0 < (1 : ℂ).re)
  rw [he] at hi
  have hre := hi.re
  change Integrable (fun v => (quadraticPeriodIntegrand d k m 1 v).re) _ at hre
  simpa only [quadraticPeriod_one_real, Complex.ofReal_re] using hre

theorem integral_realQuadraticWeight {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {m : ℝ} (hm : 0 < m) :
    (∫ v, realQuadraticWeight d k m v ∂independentMeasure d) =
      constrainedGaussianIntegral d * ((k - α - 1).factorial : ℝ) /
        (((k - 1).factorial : ℝ) * m ^ (k - α)) := by
  have he : α + (k - α - 1) + 1 = k := by omega
  have he' : α + (k - α - 1) = k - 1 := by omega
  have he'' : k - α - 1 + 1 = k - α := by omega
  have h := integral_quadraticPeriod_integer hd hα (k - α - 1) hm (by norm_num : 0 < (1 : ℂ).re)
  rw [he, he', he'', one_pow, mul_one] at h
  simp_rw [quadraticPeriod_one_real] at h
  rw [integral_complex_ofReal] at h
  have hc : Complex.ofReal (∫ v, realQuadraticWeight d k m v ∂independentMeasure d) =
      ((constrainedGaussianIntegral d * ((k - α - 1).factorial : ℝ) /
        (((k - 1).factorial : ℝ) * m ^ (k - α)) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow] using h
  exact Complex.ofReal_injective hc

theorem integral_realQuadraticWeight_mass_square {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {m w : ℝ} (hm : 0 < m) (hw : w ≠ 0) :
    (∫ v, realQuadraticWeight d k (m * w ^ 2) v ∂independentMeasure d) =
      (∫ v, realQuadraticWeight d k m v ∂independentMeasure d) / |w| ^ (2 * (k - α)) := by
  rw [integral_realQuadraticWeight hd hα hk (mul_pos hm (sq_pos_of_ne_zero hw)),
    integral_realQuadraticWeight hd hα hk hm, mul_pow, pow_mul, sq_abs]
  ring

theorem norm_setIntegral_le_realQuadraticWeight {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    {E : Set (constrainedPlane d)} (hE : MeasurableSet E) {F : constrainedPlane d → ℂ}
    (hF : IntegrableOn F E (independentMeasure d))
    (hbound : ∀ v ∈ E, ‖F v‖ ≤ C * realQuadraticWeight d k m v) :
    ‖∫ v in E, F v ∂independentMeasure d‖ ≤
      C * (constrainedGaussianIntegral d * ((k - α - 1).factorial : ℝ) /
        (((k - 1).factorial : ℝ) * m ^ (k - α))) := by
  have hw := realQuadraticWeight_integrable hd hα hk hm
  calc
    _ ≤ ∫ v in E, ‖F v‖ ∂independentMeasure d := norm_integral_le_integral_norm _
    _ ≤ ∫ v in E, C * realQuadraticWeight d k m v ∂independentMeasure d :=
      integral_mono_ae hF.norm (hw.const_mul C).integrableOn
        ((ae_restrict_mem hE).mono (fun v hv => hbound v hv))
    _ ≤ ∫ v, C * realQuadraticWeight d k m v ∂independentMeasure d :=
      setIntegral_le_integral (hw.const_mul C) (Eventually.of_forall (fun v =>
        mul_nonneg hC (realQuadraticWeight_nonneg d k hm.le v)))
    _ = _ := by rw [integral_const_mul, integral_realQuadraticWeight hd hα hk hm]

end
end IsingBulk.AnisoF002.NegativeHT.Angular
