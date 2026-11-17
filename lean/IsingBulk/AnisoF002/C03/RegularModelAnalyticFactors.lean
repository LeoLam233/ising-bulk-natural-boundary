import IsingBulk.AnisoF002.C03.RegularCollisionBlowup
import IsingBulk.AnisoF002.NegativeHT.GammaCorrection
import IsingBulk.AnisoF002.NegativeHT.ComplexModel
import IsingBulk.AnisoF002.NegativeHT.RealCyclePhase
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The actual analytic finite factors of the negative first-winding model

The inverse particle coordinate is x=1/n.  The winding temperature,
curvature, and normalized temperature are the literal trigonometric
functions in frozen F002.  Their logarithms are analytic even functions
near x=0.  Their quadratic zeros are filled by checked divided
differences, rather than by a differentiated asymptotic remainder.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem actualModel_complexSinc_even (z : ℂ) : complexSinc (-z) = complexSinc z := by
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  · apply mul_left_cancel₀ hz
    have h := complexSinc_mul (-z)
    rw [Complex.sin_neg] at h
    linear_combination -h - complexSinc_mul z

theorem analytic_even_deriv_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) : deriv f 0 = 0 := by
  have hdf : HasDerivAt f (deriv f 0) (-(0 : ℂ)) := by
    simpa only [neg_zero] using hf.differentiableAt.hasDerivAt
  have hn := hdf.comp (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).neg)
  change HasDerivAt (fun z : ℂ => f (-z)) (deriv f 0 * -1) 0 at hn
  have hfun : (fun z : ℂ => f (-z)) = f := funext he
  rw [hfun] at hn
  have h := hn.unique hf.differentiableAt.hasDerivAt
  linear_combination -h / 2

def analyticSquareFill (f : ℂ → ℂ) : ℂ → ℂ := dslope (dslope f 0) 0

theorem analyticSquareFill_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (analyticSquareFill f) 0 :=
  analyticAt_dslope_center (analyticAt_dslope_center hf)

theorem analyticSquareFill_identity {f : ℂ → ℂ} (hd : deriv f 0 = 0) (z : ℂ) :
    f z = f 0 + z ^ 2 * analyticSquareFill f z := by
  have h1 := sub_smul_dslope f 0 z
  have h2 := sub_smul_dslope (dslope f 0) 0 z
  simp only [sub_zero, smul_eq_mul, dslope_same, hd, sub_zero] at h1 h2
  change z * dslope f 0 z = f z - f 0 at h1
  change z * analyticSquareFill f z = dslope f 0 z at h2
  rw [← h2] at h1
  linear_combination -h1

theorem analyticSquareFill_even {f : ℂ → ℂ} (hd : deriv f 0 = 0)
    (he : ∀ z, f (-z) = f z) (z : ℂ) :
    analyticSquareFill f (-z) = analyticSquareFill f z := by
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  · have h1 := analyticSquareFill_identity hd (-z)
    have h2 := analyticSquareFill_identity hd z
    rw [he, neg_sq] at h1
    apply mul_left_cancel₀ (pow_ne_zero 2 hz)
    linear_combination h2 - h1

def inverseParticleTemperature (x : ℂ) : ℂ := 1 - Complex.cos ((Real.pi : ℂ) * x)

def inverseParticleCurvature (B : ℂ → ℂ) (c s : ℝ) (x : ℂ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * x) -
    B (inverseParticleTemperature x) * (c : ℂ) / (s : ℂ) ^ 2 *
      Complex.sin ((Real.pi : ℂ) * x) ^ 2

def inverseParticleLogB (B : ℂ → ℂ) (x : ℂ) : ℂ :=
  Complex.log (B (inverseParticleTemperature x))

def inverseParticleLogCurvature (B : ℂ → ℂ) (c s : ℝ) (x : ℂ) : ℂ :=
  Complex.log (inverseParticleCurvature B c s x)

def inverseParticleLogTemperature (x : ℂ) : ℂ :=
  2 * Complex.log (complexSinc ((Real.pi : ℂ) * x / 2))

theorem inverseParticleTemperature_zero : inverseParticleTemperature 0 = 0 := by
  simp [inverseParticleTemperature]

theorem inverseParticleTemperature_analytic (x : ℂ) :
    AnalyticAt ℂ inverseParticleTemperature x :=
  analyticAt_const.sub (Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))

theorem inverseParticleTemperature_even (x : ℂ) :
    inverseParticleTemperature (-x) = inverseParticleTemperature x := by
  simp only [inverseParticleTemperature, mul_neg, Complex.cos_neg]

theorem inverseParticleCurvature_zero (B : ℂ → ℂ) (c s : ℝ) :
    inverseParticleCurvature B c s 0 = 1 := by
  simp [inverseParticleCurvature]

theorem inverseParticleCurvature_analytic {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (c s : ℝ) :
    AnalyticAt ℂ (inverseParticleCurvature B c s) 0 := by
  have ht := hB.comp_of_eq (inverseParticleTemperature_analytic 0) inverseParticleTemperature_zero
  exact (Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id)).sub
    (((ht.mul analyticAt_const).div_const).mul
      ((Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)).pow 2))

theorem inverseParticleCurvature_even (B : ℂ → ℂ) (c s : ℝ) (x : ℂ) :
    inverseParticleCurvature B c s (-x) = inverseParticleCurvature B c s x := by
  simp only [inverseParticleCurvature, mul_neg, Complex.cos_neg, Complex.sin_neg, neg_sq,
    inverseParticleTemperature_even]

theorem inverseParticleLogB_analytic {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) : AnalyticAt ℂ (inverseParticleLogB B) 0 := by
  exact (hB.comp_of_eq (inverseParticleTemperature_analytic 0)
    inverseParticleTemperature_zero).clog
    (by simpa only [Function.comp_def, inverseParticleTemperature_zero] using hslit)

theorem inverseParticleLogCurvature_analytic {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (c s : ℝ) :
    AnalyticAt ℂ (inverseParticleLogCurvature B c s) 0 := by
  exact (inverseParticleCurvature_analytic hB c s).clog
    (by rw [inverseParticleCurvature_zero]; simp)

theorem inverseParticleLogTemperature_analytic : AnalyticAt ℂ inverseParticleLogTemperature 0 := by
  have hsin : AnalyticAt ℂ (fun x : ℂ => complexSinc ((Real.pi : ℂ) * x / 2)) 0 :=
    (complexSinc_analyticAt _).comp ((analyticAt_const.mul analyticAt_id).div_const)
  exact analyticAt_const.mul (hsin.clog (by simp))

theorem inverseParticleLogB_even (B : ℂ → ℂ) (x : ℂ) :
    inverseParticleLogB B (-x) = inverseParticleLogB B x := by
  simp only [inverseParticleLogB, inverseParticleTemperature_even]

theorem inverseParticleLogCurvature_even (B : ℂ → ℂ) (c s : ℝ) (x : ℂ) :
    inverseParticleLogCurvature B c s (-x) = inverseParticleLogCurvature B c s x := by
  simp only [inverseParticleLogCurvature, inverseParticleCurvature_even]

theorem inverseParticleLogTemperature_even (x : ℂ) :
    inverseParticleLogTemperature (-x) = inverseParticleLogTemperature x := by
  simp only [inverseParticleLogTemperature, mul_neg, neg_div, actualModel_complexSinc_even]

theorem inverseParticleLogB_zero (B : ℂ → ℂ) : inverseParticleLogB B 0 = Complex.log (B 0) := by
  rw [inverseParticleLogB, inverseParticleTemperature_zero]

theorem inverseParticleLogCurvature_zero (B : ℂ → ℂ) (c s : ℝ) :
    inverseParticleLogCurvature B c s 0 = 0 := by
  rw [inverseParticleLogCurvature, inverseParticleCurvature_zero, Complex.log_one]

theorem inverseParticleLogTemperature_zero : inverseParticleLogTemperature 0 = 0 := by
  simp [inverseParticleLogTemperature]

theorem inverseParticleTemperature_reciprocal (n : ℕ) :
    inverseParticleTemperature (n : ℂ)⁻¹ = (windingTau n : ℂ) := by
  simp only [inverseParticleTemperature, windingTau, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_cos, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

theorem inverseParticleCurvature_reciprocal (B : ℂ → ℂ) (c s : ℝ) (n : ℕ) :
    inverseParticleCurvature B c s (n : ℂ)⁻¹ =
      firstWindingCurvature n (B (windingTau n : ℂ)) c s := by
  simp only [inverseParticleCurvature, inverseParticleTemperature_reciprocal,
    firstWindingCurvature, Complex.ofReal_cos, Complex.ofReal_sin, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem inverseParticleTemperature_filled (x : ℂ) :
    inverseParticleTemperature x =
      ((Real.pi : ℂ) ^ 2 / 2) * x ^ 2 * complexSinc ((Real.pi : ℂ) * x / 2) ^ 2 := by
  rw [inverseParticleTemperature, one_sub_cos_filled]
  ring

theorem actual_model_logarithm_fills {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c s : ℝ) :
    ∃ U V E : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ AnalyticAt ℂ V 0 ∧ AnalyticAt ℂ E 0 ∧
      (∀ x, U (-x) = U x ∧ V (-x) = V x ∧ E (-x) = E x) ∧
      (∀ x, inverseParticleLogB B x = Complex.log (B 0) + x ^ 2 * U x) ∧
      (∀ x, inverseParticleLogCurvature B c s x = x ^ 2 * V x) ∧
      (∀ x, inverseParticleLogTemperature x = x ^ 2 * E x) := by
  have hb := inverseParticleLogB_analytic hB hslit
  have hh := inverseParticleLogCurvature_analytic hB c s
  have he := inverseParticleLogTemperature_analytic
  have hbd := analytic_even_deriv_zero hb (inverseParticleLogB_even B)
  have hhd := analytic_even_deriv_zero hh (inverseParticleLogCurvature_even B c s)
  have hed := analytic_even_deriv_zero he inverseParticleLogTemperature_even
  refine ⟨analyticSquareFill (inverseParticleLogB B),
    analyticSquareFill (inverseParticleLogCurvature B c s),
    analyticSquareFill inverseParticleLogTemperature,
    analyticSquareFill_analytic hb, analyticSquareFill_analytic hh, analyticSquareFill_analytic he,
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨analyticSquareFill_even hbd (inverseParticleLogB_even B) x,
      analyticSquareFill_even hhd (inverseParticleLogCurvature_even B c s) x,
      analyticSquareFill_even hed inverseParticleLogTemperature_even x⟩
  · intro x
    simpa only [inverseParticleLogB_zero] using analyticSquareFill_identity hbd x
  · intro x
    simpa only [inverseParticleLogCurvature_zero, zero_add] using analyticSquareFill_identity hhd x
  · intro x
    simpa only [inverseParticleLogTemperature_zero, zero_add] using analyticSquareFill_identity hed x

end
end IsingBulk.AnisoF002.NegativeHT
