import IsingBulk.Tail.SelectorSmoothDensity
import IsingBulk.Tail.SelectorPeriodicity
import IsingBulk.Tail.SelectorWeights
import IsingBulk.Analysis.LieIntegration
import IsingBulk.First.CompactParameterContinuity

/-! Periodic weighted integration for the literal source homotopy.
Spatial flux cancellation is proved from the actual face equality. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

 def coordDeriv {N : ℕ} (g : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  deriv (fun u => g (Function.update θ i u)) (θ i)

 theorem coordDeriv_eq_fderiv {N : ℕ} (g : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g θ) (i : Fin N) :
    coordDeriv g θ i = fderiv ℝ g θ (Pi.single i 1) := by
  have hd := hg.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
    (hasDerivAt_update θ i (θ i)) (by simp)
  simpa only [Function.comp_def,coordDeriv] using hd.deriv

 theorem coordDeriv_continuous {N : ℕ} (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiff ℝ ∞ g) (i : Fin N) : Continuous (fun θ => coordDeriv g θ i) := by
  have he : (fun θ => coordDeriv g θ i) = (fun θ => fderiv ℝ g θ (Pi.single i 1)) :=
    funext (fun θ => coordDeriv_eq_fderiv g θ (hg.differentiable (by simp) θ) i)
  rw [he]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

 theorem coordDeriv_mul {N : ℕ} (g h : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g θ) (hh : DifferentiableAt ℝ h θ) (i : Fin N) :
    coordDeriv (fun x => g x*h x) θ i = coordDeriv g θ i*h θ+g θ*coordDeriv h θ i := by
  have hdg := hg.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
    (hasDerivAt_update θ i (θ i)) (by simp)
  have hdh := hh.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
    (hasDerivAt_update θ i (θ i)) (by simp)
  have hd := (hdg.fun_mul hdh).deriv
  rw [coordDeriv_eq_fderiv g θ hg,coordDeriv_eq_fderiv h θ hh]
  simpa only [Function.comp_def,Function.update_eq_self,coordDeriv] using hd

 theorem divergence_eq_coords {n : ℕ} (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hF : ∀ i, Differentiable ℝ (fun θ => F θ i)) (θ : Fin (n+1) → ℝ) :
    IsingBulk.Lie.divergence F θ = ∑ i, coordDeriv (fun x => F x i) θ i := by
  unfold IsingBulk.Lie.divergence
  apply Finset.sum_congr rfl
  intro i _
  exact (coordDeriv_eq_fderiv _ θ (hF i θ) i).symm

 theorem periodic_divergence_integral_zero {n : ℕ}
    (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hF : ∀ i, ContDiff ℝ ∞ (fun θ => F θ i))
    (hp : ∀ i, CoordinatePeriodic (n+1) (fun θ => F θ i)) :
    (∫ θ in angleBox (n+1), IsingBulk.Lie.divergence F θ) = 0 := by
  have hc : Continuous (IsingBulk.Lie.divergence F) := by
    unfold IsingBulk.Lie.divergence
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  unfold angleBox
  rw [IsingBulk.Lie.integral_divergence_eq_flux (fun _ => 0) (fun _ => 2*Real.pi)
    (fun _ => Real.two_pi_pos.le) F
    (fun i => (hF i).continuous.continuousOn)
    (fun θ _ i => (hF i).differentiable (by simp) θ)
    (hc.continuousOn.integrableOn_compact isCompact_Icc),
    IsingBulk.Lie.periodic_boundaryFlux_zero _ _ F
      (fun i x => coordinatePeriodic_faces (hp i) i x)]

 theorem periodic_weighted_integration_by_parts {n : ℕ}
    (g : (Fin (n+1) → ℝ) → ℂ) (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hg : ContDiff ℝ ∞ g) (hF : ∀ i, ContDiff ℝ ∞ (fun θ => F θ i))
    (hgp : CoordinatePeriodic (n+1) g)
    (hFp : ∀ i, CoordinatePeriodic (n+1) (fun θ => F θ i)) :
    (∫ θ in angleBox (n+1), g θ*IsingBulk.Lie.divergence F θ) =
      -(∫ θ in angleBox (n+1), ∑ i, coordDeriv g θ i*F θ i) := by
  have hd : ∀ θ, IsingBulk.Lie.divergence (fun x i => g x*F x i) θ =
      g θ*IsingBulk.Lie.divergence F θ + ∑ i, coordDeriv g θ i*F θ i := by
    intro θ
    rw [divergence_eq_coords _ (fun i => (hg.mul (hF i)).differentiable (by simp)),
      divergence_eq_coords F (fun i => (hF i).differentiable (by simp))]
    simp_rw [coordDeriv_mul g _ θ (hg.differentiable (by simp) θ)
      ((hF _).differentiable (by simp) θ)]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,add_comm]
  have hz := periodic_divergence_integral_zero (fun x i => g x*F x i)
    (fun i => hg.mul (hF i)) (fun i x j => by
      dsimp only
      rw [hgp x j]
      congr 1
      exact hFp i x j)
  have hda : Continuous (IsingBulk.Lie.divergence F) := by
    unfold IsingBulk.Lie.divergence
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdb : Continuous (fun θ => ∑ i, coordDeriv g θ i*F θ i) := by
    apply continuous_finsetSum
    intro i _
    exact (coordDeriv_continuous g hg i).mul (hF i).continuous
  simp_rw [hd] at hz
  have hA : IntegrableOn (fun θ => g θ*IsingBulk.Lie.divergence F θ) (angleBox (n+1)) :=
    (hg.continuous.mul hda).continuousOn.integrableOn_compact isCompact_Icc
  have hB : IntegrableOn (fun θ => ∑ i, coordDeriv g θ i*F θ i) (angleBox (n+1)) :=
    hdb.continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_add hA hB] at hz
  exact eq_neg_of_add_eq_zero_left hz

 theorem angularSelector_contDiff {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f) :
    ContDiff ℝ ∞ (angularSelector (N := N) f) := by
  have ha := hf.a_smooth
  unfold angularSelector selectorWeight
  fun_prop

 theorem complexSelector_contDiff {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => (angularSelector f θ:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (angularSelector_contDiff f hf)

 theorem coordDeriv_selector {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (θ : Fin N → ℝ) (i : Fin N) :
    coordDeriv (fun x => (angularSelector f x:ℂ)) θ i = (namedSelectorDerivative f i θ:ℂ) := by
  have hw := (angularSelector_contDiff (N := N) f hf).differentiable (by simp) θ
  have hu := hw.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
    (hasDerivAt_update θ i (θ i)) (by simp)
  have hd : HasDerivAt (fun u => angularSelector f (Function.update θ i u))
      (namedSelectorDerivative f i θ) (θ i) := by
    have hd' := hu.differentiableAt.hasDerivAt
    simp only [Function.comp_def] at hd'
    rw [angularSelector_coordinate_deriv f θ i (hf.a_smooth.differentiable (by simp) (θ i))] at hd'
    exact hd'
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (θ i) hd
  simpa only [coordDeriv,Function.comp_def,Complex.ofRealCLM_apply] using hc.deriv

 theorem source_flux_contDiff {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    ContDiff ℝ ∞ (fun θ => homotopyFlux f r τ lam s θ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have h := homotopyFlux_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ q
  exact h.comp θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem source_spatial_current (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), (angularSelector f θ:ℂ)*
      deriv (fun u => pulledDensity f r τ u s θ) lam) =
      ∫ θ in angleBox (n+1), ∑ i, namedCurrentDensity f r τ lam s i θ := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => homotopyFlux f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    source_flux_contDiff (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => pulledDensity f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [source_pointwise_conservation (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  have hi := periodic_weighted_integration_by_parts (fun θ => (angularSelector f θ:ℂ)) F
    (complexSelector_contDiff f hf) hF
    (fun θ i => congrArg Complex.ofReal (angularSelector_periodic f hf θ i))
    (fun i => homotopyFlux_periodic (n+1) f hf hr τ lam s i)
  have hsum (θ : Fin (n+1) → ℝ) : (∑ i, namedCurrentDensity f r τ lam s i θ) =
      -(∑ i, coordDeriv (fun x => (angularSelector f x:ℂ)) θ i*F θ i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordDeriv_selector f hf]
    by_cases hd : namedSelectorDerivative f i θ = 0
    · simp [namedCurrentDensity,hd]
    · obtain ⟨hp,hp',hm,hm'⟩ := hf.named (θ i) (namedSelectorDerivative_support f θ i hd).1
      dsimp [F]
      rw [homotopyFlux_named f hr τ lam s θ i hp hp' hm hm']
      unfold namedCurrentDensity
      ring
  simp_rw [hpoint,hsum,integral_neg]
  exact hi

 theorem source_spatial_unweighted (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), deriv (fun u => pulledDensity f r τ u s θ) lam) = 0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => homotopyFlux f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    source_flux_contDiff (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => pulledDensity f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [source_pointwise_conservation (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  simp_rw [hpoint]
  exact periodic_divergence_integral_zero F hF
    (fun i => homotopyFlux_periodic (n+1) f hf hr τ lam s i)

end
end IsingBulk.Tail
