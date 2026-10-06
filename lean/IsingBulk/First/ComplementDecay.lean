import IsingBulk.First.ComplementIBP

/-! Exact radial scaling of the full transpose and arbitrary-order decay. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Phase-direction scaling is computed from the actual derivative. -/
theorem phaseDirection_const_mul (e : E) {g : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (r : ℂ) (x : E) :
    phaseDirection e (fun y => r * g y) x = r * phaseDirection e g x := by
  unfold phaseDirection
  rw [fderiv_const_mul (hg.differentiable (by simp) x) r]
  rfl

/-- One transpose lowers radial degree by precisely one, including all
coefficient derivatives. This is an exact equality, not an asymptotic assertion. -/
theorem phaseTranspose_const_mul (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) (r c : ℂ) :
    phaseTranspose e (fun y => r * g y) (fun y => c * A y) =
      fun x => (c / r) * phaseTranspose e g A x := by
  have hq := contDiff_quotient_of_support A (phaseDirection e g) hA
    (contDiff_phaseDirection e hg) hne
  have heq : (fun y => c * A y / phaseDirection e (fun z => r * g z) y) =
      fun y => (c / r) * (A y / phaseDirection e g y) := by
    funext y
    rw [phaseDirection_const_mul e hg]
    exact mul_div_mul_comm c (A y) r (phaseDirection e g y)
  funext x
  unfold phaseTranspose
  rw [heq, fderiv_const_mul (hq.differentiable (by simp) x) (c / r)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The exact q-step radial power. -/
theorem phaseTransposeIter_const_mul (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) (r : ℂ) (q : ℕ) :
    phaseTransposeIter e (fun y => r * g y) A q =
      fun x => r⁻¹ ^ q * phaseTransposeIter e g A q x := by
  induction q with
  | zero => simp [phaseTransposeIter]
  | succ q ih =>
    change phaseTranspose e (fun y => r * g y) (phaseTransposeIter e (fun y => r * g y) A q) = _
    rw [ih]
    have hr := phaseTransposeIter_regularity e hg hA hc hne q
    rw [phaseTranspose_const_mul e hg hr.1 (fun x hx => hne x (hr.2.2 hx))]
    funext x
    simp only [phaseTransposeIter, pow_succ, div_eq_mul_inv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A complete source-equivalent fixed-phase decay estimate. The constant is
the integral norm of the actual normalized q-fold transpose amplitude. -/
theorem integral_nonstationary_decay (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0)
    (hreal : ∀ x ∈ tsupport A, (g x).re ≤ 0) (q : ℕ) (R : ℝ) (hR : 0 < R) :
    ‖∫ x, A x * Complex.exp ((R : ℂ) * g x) ∂μ‖ ≤
      R⁻¹ ^ q * ∫ x, ‖phaseTransposeIter e g A q x‖ ∂μ := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hscaled : ContDiff ℝ ∞ (fun y => (R : ℂ) * g y) := contDiff_const.mul hg
  have hnscaled : ∀ x ∈ tsupport A, phaseDirection e (fun y => (R : ℂ) * g y) x ≠ 0 := by
    intro x hx
    rw [phaseDirection_const_mul e hg]
    exact mul_ne_zero hRc (hne x hx)
  rw [integral_phaseTransposeIter e hscaled hA hc hnscaled q,
    phaseTransposeIter_const_mul e hg hA hc hne]
  have heq : (fun x => (R : ℂ)⁻¹ ^ q * phaseTransposeIter e g A q x *
      Complex.exp ((R : ℂ) * g x)) =
      fun x => (R : ℂ)⁻¹ ^ q * (phaseTransposeIter e g A q x *
        Complex.exp ((R : ℂ) * g x)) := by funext x; ring
  rw [heq, integral_const_mul, norm_mul, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hr := phaseTransposeIter_regularity e hg hA hc hne q
  have hint := (hr.1.continuous.integrable_of_hasCompactSupport (μ := μ) hr.2.1).norm
  apply norm_integral_le_of_norm_le hint
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ tsupport A
  · have hnorm : ‖Complex.exp ((R : ℂ) * g x)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simpa using mul_nonpos_of_nonneg_of_nonpos hR.le (hreal x hx)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hnorm
  · have hz : phaseTransposeIter e g A q x = 0 := by
      by_contra hz
      exact hx (hr.2.2 (subset_closure hz))
    simp [hz]

end
end IsingBulk.First
