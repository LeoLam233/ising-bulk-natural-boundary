import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticParameterIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Analytic division by a coordinate, constructed by an actual parameter integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def coordinateContraction (s : ℝ) : (E × ℂ) →L[ℂ] (E × ℂ) :=
  (ContinuousLinearMap.inl ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ E ℂ) +
    (s : ℂ) • (ContinuousLinearMap.inr ℂ E ℂ).comp (ContinuousLinearMap.snd ℂ E ℂ)

@[simp] theorem coordinateContraction_apply (s : ℝ) (z : E × ℂ) :
    coordinateContraction s z = (z.1,(s : ℂ)*z.2) := by
  simp [coordinateContraction]

theorem coordinateContraction_continuous :
    Continuous (coordinateContraction : ℝ → (E × ℂ) →L[ℂ] (E × ℂ)) :=
  continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

theorem coordinateContraction_norm (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖coordinateContraction (E := E) s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [coordinateContraction_apply,Prod.norm_def,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hs.1,one_mul]
  exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) hs.2)

def coordinateHadamard (f : E × ℂ → ℂ) (z : E × ℂ) : ℂ :=
  ∫ s : ℝ in Icc 0 1, fderiv ℂ f (coordinateContraction s z) (0,1)

theorem coordinateHadamard_analyticAt {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (coordinateHadamard f) 0 := by
  let L : ((E × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,1)
  exact analyticAt_integral_linear_contractions _ ((L.analyticAt _).comp hf.fderiv)
    coordinateContraction coordinateContraction_continuous coordinateContraction_norm

@[simp] theorem coordinateHadamard_zero (f : E × ℂ → ℂ) :
    coordinateHadamard f 0 = fderiv ℂ f 0 (0,1) := by
  simp [coordinateHadamard]
  rfl

/-- The quotient is analytic on the whole neighborhood, including the divisor itself. -/
theorem coordinateHadamard_identity {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ z : E × ℂ in 𝓝 0, f z - f (z.1,0) = z.2 * coordinateHadamard f z := by
  let g : E × ℂ → ℂ := fun z => fderiv ℂ f z (0,1)
  let L : ((E × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,1)
  have hg : AnalyticAt ℂ g 0 := by
    convert! ((L.analyticAt _).comp hf.fderiv) using 1
  obtain ⟨r,hr,hrf⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  filter_upwards [Metric.ball_mem_nhds (0 : E × ℂ) hr] with z hz
  have hz' : ‖z‖ < r := by simpa using hz
  have hlocal (s : ℝ) (hs : s ∈ Icc 0 1) :
      AnalyticAt ℂ f (coordinateContraction s z) ∧
      AnalyticAt ℂ g (coordinateContraction s z) := by
    apply hrf
    simp only [dist_zero_right]
    calc
      ‖coordinateContraction s z‖ ≤ ‖coordinateContraction (E := E) s‖ * ‖z‖ :=
        (coordinateContraction s).le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (coordinateContraction_norm s hs) (norm_nonneg z)
      _ < r := by simpa using hz'
  have hcurve : Continuous (fun s : ℝ => coordinateContraction s z) := by
    simp only [coordinateContraction_apply]
    fun_prop
  have hc : ContinuousOn (fun s : ℝ => g (coordinateContraction s z)) (Icc 0 1) := by
    intro s hs
    exact ((hlocal s hs).2.continuousAt.comp (f := fun u : ℝ => coordinateContraction u z)
      hcurve.continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun s : ℝ => z.2 * g (coordinateContraction s z))
      volume 0 1 := (hc.const_mul z.2).intervalIntegrable_of_Icc (by norm_num)
  have hd (s : ℝ) (hs : s ∈ uIcc 0 1) :
      HasDerivAt (fun u : ℝ => f (z.1,(u : ℂ)*z.2))
        (z.2 * g (coordinateContraction s z)) s := by
    have hs' : s ∈ Icc 0 1 := by simpa using hs
    have hfa : DifferentiableAt ℂ f (z.1,(s : ℂ)*z.2) := by
      simpa using (hlocal s hs').1.differentiableAt
    have hline : HasDerivAt (fun u : ℂ => (z.1,u*z.2)) (0,z.2) (s : ℂ) := by
      simpa using (hasDerivAt_const (s : ℂ) z.1).prodMk ((hasDerivAt_id (s : ℂ)).mul_const z.2)
    have h := (hfa.hasFDerivAt.comp_hasDerivAt (f := fun u : ℂ => (z.1,u*z.2)) (s : ℂ) hline).comp_ofReal
    have heval : fderiv ℂ f (z.1,(s : ℂ)*z.2) ((0 : E),z.2) =
        z.2 * g (coordinateContraction s z) := by
      rw [show ((0 : E),z.2) = z.2 • ((0 : E),(1 : ℂ)) by simp]
      rw [map_smul]
      simp only [g,coordinateContraction_apply,smul_eq_mul]
    rw [heval] at h
    convert! h using 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa [coordinateHadamard,g] using h.symm

end IsingBulk.Anisotropic.NegativeNormalForm
