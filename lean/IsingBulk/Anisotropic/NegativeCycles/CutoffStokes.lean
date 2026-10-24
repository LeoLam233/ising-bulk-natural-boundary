import IsingBulk.Anisotropic.NegativeCycles.CutoffDerivative

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter MeasureTheory
open scoped Topology

theorem cutoff_form_contDiff {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ)
    (hω : ∀x∈tsupport χ, ContDiffAt ℝ 1 ω x) :
    ContDiff ℝ 1 (fun x => χ x • ω x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport χ
  · exact hχ.contDiffAt.smul (hω x hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoff_form_eventually_zero ω hx)

theorem cutoff_closed_extDeriv {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ)
    (hω : ∀x∈tsupport χ, ContDiffAt ℝ 1 ω x)
    (hc : ∀x∈tsupport χ, extDeriv ω x=0) (x : ParameterSpace n) :
    extDeriv (fun y => χ y • ω y) x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))=
      cutoffError χ ω x := by
  by_cases hx : x∈tsupport χ
  · rw [extDeriv_cutoff_apply (hχ.differentiable one_ne_zero x)
      ((hω x hx).differentiableAt one_ne_zero),hc x hx]
    simp
  · have hz : χ=ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hd : fderiv ℝ χ x=0 := by rw [hz.fderiv_eq]; simp
    rw [(cutoff_form_eventually_zero ω hx).extDeriv_eq]
    simp [extDeriv,cutoffError,hd,←ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

/-- Fixed-ball cutoffs give exact Stokes transport with an explicit annular
integral. All integrability is proved from C¹ regularity on the support. -/
theorem cutoff_box_stokes {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ)
    (hω : ∀x∈tsupport χ, ContDiffAt ℝ 1 ω x)
    (hc : ∀x∈tsupport χ, extDeriv ω x=0)
    {a b : ParameterSpace n} (hab : a≤b) :
    boxBoundaryFlux (fun x => χ x • ω x) a b=
      ∫ x in Icc a b, cutoffError χ ω x := by
  have hf := cutoff_form_contDiff hχ hω
  have he : Continuous (extDeriv (fun x => χ x • ω x)) := by
    change Continuous (fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      (fderiv ℝ (fun y => χ y • ω y) x))
    simpa only [Function.comp_def,ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ParameterSpace n) ℂ).continuous.comp
        (hf.continuous_fderiv one_ne_zero)
  rw [boxBoundaryFlux_eq_integral_extDeriv _ hab
    (fun x _ => hf.differentiable one_ne_zero x)
    ((he.eval_const _).continuousOn.integrableOn_compact isCompact_Icc)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  exact cutoff_closed_extDeriv hχ hω hc x

theorem cutoffError_eq_zero_of_notMem_tsupport {n : ℕ} {χ : ParameterSpace n → ℝ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    {x : ParameterSpace n} (hx : x∉tsupport χ) : cutoffError χ ω x=0 := by
  have hz : χ=ᶠ[𝓝 x] 0 := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hd : fderiv ℝ χ x=0 := by rw [hz.fderiv_eq]; simp
  simp [cutoffError,hd]

theorem cutoffError_continuous {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ) (hω : ∀x∈tsupport χ, ContinuousAt ω x) :
    Continuous (cutoffError χ ω) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈tsupport χ
  · unfold cutoffError
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact (((hχ.continuous_fderiv one_ne_zero).continuousAt.eval_const _).smul
      ((hω x hx).eval_const _)).const_smul _
  · have hz : cutoffError χ ω=ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      exact cutoffError_eq_zero_of_notMem_tsupport ω hy
    exact continuousAt_const.congr_of_eventuallyEq hz

/-- The cutoff transport only needs pointwise differentiability of the uncut
form on the support. It does not assume an extension outside that support. -/
theorem cutoff_box_stokes_of_differentiable {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ)
    (hω : ∀x∈tsupport χ, DifferentiableAt ℝ ω x)
    (hc : ∀x∈tsupport χ, extDeriv ω x=0)
    {a b : ParameterSpace n} (hab : a≤b) :
    boxBoundaryFlux (fun x => χ x • ω x) a b=
      ∫ x in Icc a b, cutoffError χ ω x := by
  have hd (x : ParameterSpace n) : DifferentiableAt ℝ (fun y => χ y • ω y) x := by
    by_cases hx : x∈tsupport χ
    · exact (hχ.differentiable one_ne_zero x).smul (hω x hx)
    · exact (cutoff_form_eventually_zero ω hx).differentiableAt_iff.mpr (differentiableAt_const _)
  have he (x : ParameterSpace n) :
      extDeriv (fun y => χ y • ω y) x (fun k => (Pi.single k (1:ℝ) : ParameterSpace n))=
        cutoffError χ ω x := by
    by_cases hx : x∈tsupport χ
    · rw [extDeriv_cutoff_apply (hχ.differentiable one_ne_zero x) (hω x hx),hc x hx]
      simp
    · rw [(cutoff_form_eventually_zero ω hx).extDeriv_eq,cutoffError_eq_zero_of_notMem_tsupport ω hx]
      simp [extDeriv,←ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  have hi : IntegrableOn (cutoffError χ ω) (Icc a b) := (cutoffError_continuous hχ (fun x hx => (hω x hx).continuousAt)).continuousOn.integrableOn_compact
    (K := Icc a b) isCompact_Icc
  rw [boxBoundaryFlux_eq_integral_extDeriv _ hab (fun x _ => hd x)
    (hi.congr_fun (fun x _ => (he x).symm) measurableSet_Icc)]
  exact setIntegral_congr_fun measurableSet_Icc (fun x _ => he x)

end IsingBulk.Anisotropic.NegativeCycles
