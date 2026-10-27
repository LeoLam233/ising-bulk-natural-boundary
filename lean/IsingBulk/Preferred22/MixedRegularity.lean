import IsingBulk.First.ComplementMixedRegularity
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Mixed real-angular/complex-parameter regularity for the actual transport
recursion. The Cauchy--Riemann and Schwarz calculation below proves that a
real angular derivative preserves parameter holomorphy; real cutoffs require
no complex continuation. The imported First lemmas are generic calculus only. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A parameter-slice real derivative is the joint real derivative evaluated
on the corresponding parameter direction. -/
theorem mixed_parameter_slice_fderiv (A : ℂ × E → ℂ) (z : ℂ × E) (v : ℂ)
    (hA : DifferentiableAt ℝ A z) :
    fderiv ℝ (fun t : ℂ => A (t,z.2)) z.1 v=fderiv ℝ A z (v,0) := by
  have hm : HasFDerivAt (fun t : ℂ => (t,z.2)) (ContinuousLinearMap.inl ℝ ℂ E) z.1 := by
    convert! (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1) using 1
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (hA.hasFDerivAt.comp z.1 hm).fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply] using hh

theorem mixed_direction_contDiffAt (A : ℂ × E → ℂ) (z v : ℂ × E)
    (hA : ContDiffAt ℝ ∞ A z) :
    ContDiffAt ℝ ∞ (fun x => fderiv ℝ A x v) z :=
  (hA.fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiffAt_const

/-- Real angular differentiation preserves parameter holomorphy. This is the
source-specific mixed-regularity closure needed to iterate real cutoff jets. -/
theorem mixed_angular_direction_holomorphic (A : ℂ × E → ℂ) (z : ℂ × E) (e : E)
    (hA : ContDiffAt ℝ ∞ A z)
    (hhol : ∀ᶠ x : ℂ × E in 𝓝 z, DifferentiableAt ℂ (fun t => A (t,x.2)) x.1) :
    DifferentiableAt ℂ (fun t : ℂ => fderiv ℝ A (t,z.2) (0,e)) z.1 := by
  have hAD : DifferentiableAt ℝ (fderiv ℝ A) z :=
    (hA.fderiv_right (by simp : (1:ℕ∞ω)+1≤∞)).differentiableAt (by norm_num)
  have hdir (v : ℂ × E) : DifferentiableAt ℝ (fun x => fderiv ℝ A x v) z :=
    (mixed_direction_contDiffAt A z v hA).differentiableAt (by simp)
  have hsym (v w : ℂ × E) :
      fderiv ℝ (fun x => fderiv ℝ A x v) z w =
        fderiv ℝ (fun x => fderiv ℝ A x w) z v := by
    simp only [fderiv_clm_apply hAD (differentiableAt_const _),fderiv_const_apply,
      ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
    exact hA.isSymmSndFDerivAt (by simp) w v
  have hnear : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ A x := by
    filter_upwards [(hA.of_le (by simp : (1:ℕ∞ω)≤∞)).eventually (by norm_num)] with x hx
    exact hx.differentiableAt (by norm_num)
  have hCR : (fun x => fderiv ℝ A x (Complex.I,0)) =ᶠ[𝓝 z]
      (fun x => Complex.I*fderiv ℝ A x (1,0)) := by
    filter_upwards [hnear,hhol] with x hx hh
    have hc := (differentiableAt_complex_iff_differentiableAt_real.mp hh).2
    rw [mixed_parameter_slice_fderiv A x Complex.I hx,mixed_parameter_slice_fderiv A x 1 hx] at hc
    simpa only [smul_eq_mul] using hc
  have hCRd := congrArg (fun L : (ℂ × E) →L[ℝ] ℂ => L (0,e)) hCR.fderiv_eq
  rw [fderiv_const_mul (hdir (1,0)) Complex.I] at hCRd
  simp only [smul_apply,smul_eq_mul] at hCRd
  have hreal : DifferentiableAt ℝ (fun t : ℂ => fderiv ℝ A (t,z.2) (0,e)) z.1 :=
    DifferentiableAt.comp (f:=fun t : ℂ => (t,z.2))
      (g:=fun x : ℂ × E => fderiv ℝ A x (0,e)) z.1 (hdir (0,e))
      (differentiableAt_id.prodMk (differentiableAt_const _))
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hreal,?_⟩
  rw [mixed_parameter_slice_fderiv (fun x => fderiv ℝ A x (0,e)) z Complex.I (hdir (0,e)),
    mixed_parameter_slice_fderiv (fun x => fderiv ℝ A x (0,e)) z 1 (hdir (0,e))]
  rw [hsym (0,e) (Complex.I,0),hsym (0,e) (1,0)]
  simpa only [smul_eq_mul] using hCRd

/-- The parameter derivative is jointly smooth in real angles and the
complex parameter; this instantiates the proper generic mixed-calculus input. -/
theorem mixed_parameter_derivative_contDiffAt (A : ℂ × E → ℂ) (z : ℂ × E)
    (hA : ContDiffAt ℝ ∞ A z)
    (hhol : ∀ᶠ x : ℂ × E in 𝓝 z, DifferentiableAt ℂ (fun t => A (t,x.2)) x.1) :
    ContDiffAt ℝ ∞ (fun x : ℂ × E => deriv (fun t : ℂ => A (t,x.2)) x.1) z := by
  have hswap : ContDiffAt ℝ ∞ (fun x : E × ℂ => A (x.2,x.1)) (z.2,z.1) :=
    hA.comp (z.2,z.1) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hholswap : ∀ᶠ x : E × ℂ in 𝓝 (z.2,z.1),
      DifferentiableAt ℂ (fun t => A (t,x.1)) x.2 := by
    exact ((show Continuous (fun x : E × ℂ => (x.2,x.1)) by fun_prop).tendsto (z.2,z.1)).eventually hhol
  have hd := IsingBulk.First.contDiffAt_parameterized_complex_deriv z.2 z.1 hswap hholswap
  exact hd.comp z (contDiffAt_snd.prodMk contDiffAt_fst)

/-- Joint real C∞ regularity and genuine parameter holomorphy on one open
source domain. This finite base-data predicate will replace an assumption on
all recursively generated word coefficients. -/
def PreferredMixedSmoothOn (A : ℂ × E → ℂ) (Ω : Set (ℂ × E)) : Prop :=
  ∀ z∈Ω, ContDiffAt ℝ ∞ A z ∧ DifferentiableAt ℂ (fun t => A (t,z.2)) z.1

theorem PreferredMixedSmoothOn.parameter {A : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hΩ : IsOpen Ω) :
    PreferredMixedSmoothOn (fun z => deriv (fun t => A (t,z.2)) z.1) Ω := by
  intro z hz
  have hhol : ∀ᶠ x : ℂ × E in 𝓝 z, DifferentiableAt ℂ (fun t => A (t,x.2)) x.1 := by
    filter_upwards [hΩ.mem_nhds hz] with x hx
    exact (hA x hx).2
  refine ⟨mixed_parameter_derivative_contDiffAt A z (hA z hz).1 hhol,?_⟩
  have hs : AnalyticAt ℂ (fun t => A (t,z.2)) z.1 := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact ((show Continuous (fun t : ℂ => (t,z.2)) by fun_prop).tendsto z.1).eventually hhol
  exact hs.deriv.differentiableAt

theorem PreferredMixedSmoothOn.angular {A : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hΩ : IsOpen Ω) (e : E) :
    PreferredMixedSmoothOn (fun z => fderiv ℝ A z (0,e)) Ω := by
  intro z hz
  refine ⟨mixed_direction_contDiffAt A z (0,e) (hA z hz).1,?_⟩
  apply mixed_angular_direction_holomorphic A z e (hA z hz).1
  filter_upwards [hΩ.mem_nhds hz] with x hx
  exact (hA x hx).2

end
end IsingBulk.Preferred22
