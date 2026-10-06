import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! The genuine repeated transpose mechanism for FIRST's complement.
Quotients are proved smooth even where their denominators vanish outside support. -/
namespace IsingBulk.First
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E]

/-- Division cannot enlarge topological support, including totalized zero division. -/
theorem tsupport_quotient_subset (A b : E → ℂ) :
    tsupport (fun x => A x / b x) ⊆ tsupport A := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp [Function.mem_support, hx]

variable [NormedSpace ℝ E]

/-- A smooth compactly supported numerator needs denominator nonvanishing only
on its support. This proves the global smooth quotient used in integration by parts. -/
theorem contDiff_quotient_of_support (A b : E → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hne : ∀ x ∈ tsupport A, b x ≠ 0) :
    ContDiff ℝ ∞ (fun x => A x / b x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport A
  · simpa only [div_eq_mul_inv, Pi.inv_apply, Pi.mul_apply] using hA.contDiffAt.mul (hb.contDiffAt.inv (hne x hx))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have hq : (fun x => A x / b x) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hq

/-- Directional derivative of the phase. -/
def phaseDirection (e : E) (g : E → ℂ) (x : E) : ℂ := fderiv ℝ g x e

/-- The actual formal transpose, including derivatives of its denominator. -/
def phaseTranspose (e : E) (g A : E → ℂ) (x : E) : ℂ :=
  -fderiv ℝ (fun y => A y / phaseDirection e g y) x e

/-- All generated amplitudes stay on the original angular support. -/
theorem tsupport_phaseTranspose_subset (e : E) (g A : E → ℂ) :
    tsupport (phaseTranspose e g A) ⊆ tsupport A := by
  have h := (tsupport_fderiv_apply_subset ℝ e
    (f := fun y => A y / phaseDirection e g y)).trans
    (tsupport_quotient_subset A (phaseDirection e g))
  change tsupport (-fun x => fderiv ℝ (fun y => A y / phaseDirection e g y) x e) ⊆ _
  rw [tsupport_neg]
  exact h

theorem contDiff_phaseDirection (e : E) {g : E → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (phaseDirection e g) := by
  exact (hg.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const

theorem contDiff_phaseTranspose (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) :
    ContDiff ℝ ∞ (phaseTranspose e g A) := by
  have hq := contDiff_quotient_of_support A (phaseDirection e g) hA
    (contDiff_phaseDirection e hg) hne
  exact ((hq.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const).neg

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

/-- One true integration by parts with the complete transpose amplitude. -/
theorem integral_phaseTranspose (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) :
    (∫ x, A x * Complex.exp (g x) ∂μ) =
      ∫ x, phaseTranspose e g A x * Complex.exp (g x) ∂μ := by
  let Q : E → ℂ := fun x => A x / phaseDirection e g x
  have hQ := contDiff_quotient_of_support A (phaseDirection e g) hA
    (contDiff_phaseDirection e hg) hne
  have hQc : HasCompactSupport Q := by
    exact hc.of_isClosed_subset (isClosed_tsupport Q)
      (tsupport_quotient_subset A (phaseDirection e g))
  have hDQ : Continuous (fun x => fderiv ℝ Q x e) :=
    (hQ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hE : ContDiff ℝ ∞ (fun x => Complex.exp (g x)) := hg.cexp
  have hdir (x : E) : fderiv ℝ (fun y => Complex.exp (g y)) x e =
      Complex.exp (g x) * phaseDirection e g x := by
    rw [(hg.differentiable (by simp) x).hasFDerivAt.cexp.fderiv]
    rfl
  have heq (x : E) : Q x * fderiv ℝ (fun y => Complex.exp (g y)) x e =
      A x * Complex.exp (g x) := by
    rw [hdir]
    by_cases ha : A x = 0
    · simp [Q, ha]
    · have hb := hne x (subset_closure ha)
      dsimp [Q]
      field_simp
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (v := e) (f := Q) (g := fun x => Complex.exp (g x))
    ((hDQ.mul hE.continuous).integrable_of_hasCompactSupport ((hQc.fderiv_apply ℝ e).mul_right))
    (((hA.continuous.mul hE.continuous).integrable_of_hasCompactSupport hc.mul_right).congr
      (Filter.Eventually.of_forall fun x => (heq x).symm))
    ((hQ.continuous.mul hE.continuous).integrable_of_hasCompactSupport hQc.mul_right)
    (fun x _ => hQ.differentiable (by simp) x)
    (fun x _ => hE.differentiable (by simp) x)
  simpa only [heq, phaseTranspose, neg_mul, integral_neg] using hb

/-- Iteration acts on the entire preceding amplitude. -/
def phaseTransposeIter (e : E) (g A : E → ℂ) : ℕ → E → ℂ
  | 0 => A
  | n + 1 => phaseTranspose e g (phaseTransposeIter e g A n)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem phaseTransposeIter_regularity (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) (n : ℕ) :
    ContDiff ℝ ∞ (phaseTransposeIter e g A n) ∧
      HasCompactSupport (phaseTransposeIter e g A n) ∧
      tsupport (phaseTransposeIter e g A n) ⊆ tsupport A := by
  induction n with
  | zero => exact ⟨hA, hc, Subset.rfl⟩
  | succ n ih =>
    have hs := (tsupport_phaseTranspose_subset e g (phaseTransposeIter e g A n)).trans ih.2.2
    refine ⟨contDiff_phaseTranspose e hg ih.1 (fun x hx => hne x (ih.2.2 hx)), ?_, hs⟩
    exact hc.of_isClosed_subset (isClosed_tsupport _) hs

/-- Repeated integration by parts is a proved integral identity, for every q. -/
theorem integral_phaseTransposeIter (e : E) {g A : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ x ∈ tsupport A, phaseDirection e g x ≠ 0) (q : ℕ) :
    (∫ x, A x * Complex.exp (g x) ∂μ) =
      ∫ x, phaseTransposeIter e g A q x * Complex.exp (g x) ∂μ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [ih]
    have hr := phaseTransposeIter_regularity e hg hA hc hne q
    exact integral_phaseTranspose e hg hr.1 hr.2.1 (fun x hx => hne x (hr.2.2 hx))

end
end IsingBulk.First
