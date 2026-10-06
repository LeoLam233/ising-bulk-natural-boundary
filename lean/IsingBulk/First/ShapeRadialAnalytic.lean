import IsingBulk.First.ShapeRadialLimit
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Holomorphy of the actual radial period on the right coefficient half-plane. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem shapeQuadratic_right_lower {Q a : ℝ} {c : ℂ} (ha : a ≤ c.re) (r : ℝ) :
    min Q a * (1 + r ^ 2) ≤ ‖shapeQuadratic Q c r‖ := by
  have hs : (r : ℂ)^2 = ((r^2 : ℝ) : ℂ) := by norm_cast
  have hre : Q + c.re * r^2 ≤ ‖shapeQuadratic Q c r‖ := by
    simpa only [shapeQuadratic, hs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] using Complex.re_le_norm (shapeQuadratic Q c r)
  have hmQ := min_le_left Q a
  have hma := mul_le_mul_of_nonneg_right (le_trans (min_le_right Q a) ha) (sq_nonneg r)
  nlinarith

theorem shapeQuadratic_right_ne_zero {Q : ℝ} {c : ℂ} (hQ : 0 < Q) (hc : 0 < c.re)
    (r : ℝ) : shapeQuadratic Q c r ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (by positivity) (shapeQuadratic_right_lower (a := c.re) le_rfl r)

theorem shapeRadialKernel_right_integrable (k : ℕ) {Q : ℝ} {c : ℂ}
    (hQ : 0 < Q) (hc : 0 < c.re) : Integrable (shapeRadialKernel k Q c) := by
  refine ((shapeRadialMajorant_integrable k).const_mul
    ((min Q c.re) ^ (k+1))⁻¹).mono' ?_ (Eventually.of_forall fun r => ?_)
  · apply Continuous.aestronglyMeasurable
    have hcont : Continuous (shapeQuadratic Q c) := by unfold shapeQuadratic; fun_prop
    have hn : ∀ r : ℝ, shapeQuadratic Q c r ^ (k+1) ≠ 0 :=
      fun r => pow_ne_zero _ (shapeQuadratic_right_ne_zero hQ hc r)
    unfold shapeRadialKernel
    fun_prop
  · exact norm_shapeRadialKernel_le (lt_min hQ hc) (shapeQuadratic_right_lower le_rfl r)

/-- Differentiation in c raises the radial index by one, with its exact coefficient. -/
theorem shapeRadialKernel_hasDerivAt (k : ℕ) {Q : ℝ} {c : ℂ} (hQ : 0 < Q)
    (hc : 0 < c.re) (r : ℝ) :
    HasDerivAt (fun z => shapeRadialKernel k Q z r)
      (-((k+1 : ℕ) : ℂ) * shapeRadialKernel (k+1) Q c r) c := by
  have hn := shapeQuadratic_right_ne_zero hQ hc r
  have hq : HasDerivAt (fun z : ℂ => shapeQuadratic Q z r) ((r : ℂ)^2) c := by
    simpa [shapeQuadratic] using
      ((hasDerivAt_id c).mul_const ((r : ℂ)^2)).const_add (Q : ℂ)
  have hf := (hasDerivAt_const c ((r : ℂ)^(2*k))).div
    (hq.pow (k+1)) (pow_ne_zero _ hn)
  convert hf using 1
  · rfl
  · unfold shapeRadialKernel
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    rw [show 2*(k+1) = 2*k+2 by omega, pow_add]
    field_simp [hn]
    simp only [pow_succ]
    ring

/-- The parameter derivative is passed through the genuine integral on a fixed
half-plane neighborhood with one integrable majorant chosen before z. -/
theorem shapeRadialIntegral_hasDerivAt (k : ℕ) {Q : ℝ} {c : ℂ}
    (hQ : 0 < Q) (hc : 0 < c.re) :
    HasDerivAt (shapeRadialIntegral k Q)
      (∫ r : ℝ in Ioi 0, -((k+1 : ℕ) : ℂ) * shapeRadialKernel (k+1) Q c r) c := by
  let U : Set ℂ := {z | c.re/2 < z.re}
  have hU : U ∈ 𝓝 c :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [U]; linarith)
  have hu (z : ℂ) (hz : z ∈ U) : 0 < z.re := by dsimp [U] at hz; linarith
  let C : ℝ := (k+1 : ℕ) * ((min Q (c.re/2)) ^ (k+2))⁻¹
  have hm : 0 < min Q (c.re/2) := lt_min hQ (by linarith)
  have hmeas : ∀ᶠ z in 𝓝 c, AEStronglyMeasurable (shapeRadialKernel k Q z)
      (volume.restrict (Ioi 0)) := by
    filter_upwards [hU] with z hz
    exact (shapeRadialKernel_right_integrable k hQ (hu z hz)).aestronglyMeasurable.restrict
  have hfmeas : AEStronglyMeasurable
      (fun r : ℝ => -((k+1 : ℕ) : ℂ) * shapeRadialKernel (k+1) Q c r)
      (volume.restrict (Ioi 0)) :=
    ((shapeRadialKernel_right_integrable (k+1) hQ hc).const_mul _).aestronglyMeasurable.restrict
  have hb : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0), ∀ z ∈ U,
      ‖-((k+1 : ℕ) : ℂ) * shapeRadialKernel (k+1) Q z r‖ ≤
        C * shapeRadialMajorant (k+1) r := by
    apply Eventually.of_forall
    intro r z hz
    have hh := norm_shapeRadialKernel_le (m := k+1) hm
      (shapeQuadratic_right_lower (show c.re/2 ≤ z.re from le_of_lt hz) r)
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    simpa [C, Nat.add_assoc, mul_assoc] using
      (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (k+1)))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) hU hmeas
    (shapeRadialKernel_right_integrable k hQ hc).integrableOn hfmeas hb
    ((shapeRadialMajorant_integrable (k+1)).const_mul C).integrableOn
    (Eventually.of_forall (fun r z hz => shapeRadialKernel_hasDerivAt k hQ (hu z hz) r))
  exact hh.2

theorem shapeRadialIntegral_analyticOnNhd (k : ℕ) {Q : ℝ} (hQ : 0 < Q) :
    AnalyticOnNhd ℂ (shapeRadialIntegral k Q) {c : ℂ | 0 < c.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro c hc
    exact (shapeRadialIntegral_hasDerivAt k hQ hc).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end
end IsingBulk.First
