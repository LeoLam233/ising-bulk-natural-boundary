import IsingBulk.HT22.Anchor.Field
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry IsingBulk.HT22.Tail Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def regularDivergence {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ a, coordinateFrame τ p m a
    (fun s x => residualField anchor s (sourceCoordinate τ p m s x) a) t θ

theorem realSourceChart_velocity {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (h : PreferredFramePoint τ δ p m (s+(t:ℂ)) θ) :
    (preferredRealCoordinateJacobian (realSourceChart τ p m s) (t,θ))⁻¹.mulVec
      (preferredRealCoordinateSpeed (realSourceChart τ p m s) (t,θ)-
        residualField anchor (s+(t:ℂ)) (sourceCoordinate τ p m (s+(t:ℂ)) θ))=
      angularField anchor τ p m (s+(t:ℂ)) θ := by
  rw [realSourceChart_jacobian τ δ p m hp hm s t θ h,
    realSourceChart_speed τ δ p m hp hm s t θ h,
    preferredSourceJacobian_inverse τ δ p m (hp.differentiable (by simp))
      (hm.differentiable (by simp)) (s+(t:ℂ)) θ
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper]
  have hv := source_inverseV_ne_zero h
  funext i
  simp only [angularField,preferredAngularRepresentative,Matrix.mul_diagonal,
    Matrix.mulVec,dotProduct,Pi.sub_apply]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←sourceCoordinate_moving_adapter τ p m (s+(t:ℂ)) θ j,←inverseV_moving_adapter]
  field_simp [hv j]
  ring

theorem source_residual_trace {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ)
    (hB : DifferentiableAt ℝ (fun x : Fin N → ℝ => residualField anchor s (sourceCoordinate τ p m s x)) θ) :
    Matrix.trace ((preferredSourceJacobian τ p m s θ)⁻¹*
      preferredRealResidualJacobian (fun x => residualField anchor s (sourceCoordinate τ p m s x)) θ)=
      regularDivergence anchor τ p m s θ := by
  have hd (a i : Fin N) : preferredRealResidualJacobian
      (fun x => residualField anchor s (sourceCoordinate τ p m s x)) θ a i=
      deriv (fun u : ℝ => residualField anchor s (sourceCoordinate τ p m s (Function.update θ i u)) a) (θ i) := by
    have hh := (differentiableAt_pi.mp hB a).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      (hasDerivAt_update θ i (θ i)) (by simp only [Function.update_eq_self])
    exact hh.deriv.symm
  unfold regularDivergence
  simp_rw [coordinateFrame_eq_shared,
    preferredCoordinateFrame_eq_inverse_jacobian τ δ p m hp hm s θ _ _
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,hd]
  exact Finset.sum_comm

/-- Full scalar Piola equation for the actual fixed-v named-anchor field.
All derivatives come from genuine smooth source maps; there is no assumed
Jacobian equation, divergence identity or generated-scalar premise. -/
theorem coordinateJacobian_piola {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    deriv (fun t : ℂ => coordinateJacobian τ p m t θ) s-
      (∑ i, deriv (fun u : ℝ => angularField anchor τ p m s (Function.update θ i u) i*
        coordinateJacobian τ p m s (Function.update θ i u)) (θ i))=
      coordinateJacobian τ p m s θ*regularDivergence anchor τ p m s θ := by
  have h := hpoint (s,θ) hz
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  let F := realSourceChart (N:=N) τ p m s
  let B := fun x : Fin N → ℝ => residualField anchor s (sourceCoordinate τ p m s x)
  have hF : ContDiffAt ℝ ∞ F (0,θ) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      realSourceChart_contDiffAt τ p m hp hm s 0 θ (by simpa using h.trace_im) (by simpa using h.upper)
  have hBs : ∀ i, PreferredMixedSmoothOn
      (fun z => residualField anchor z.1 (sourceCoordinate τ p m z.1 z.2) i) Ω := by
    intro i
    apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun z => residualField anchor z.1 z.2 i)
    intro z hz
    exact analyticAt_pi_iff.mp (residualField_analyticAt anchor z.1 _
      (framePoint_inverse_analytic (hpoint z hz)) (source_inverseV_ne_zero (hpoint z hz) anchor)) i
  have hB : DifferentiableAt ℝ B θ := by
    apply differentiableAt_pi.mpr
    intro i
    exact ((hBs i (s,θ) hz).1.comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hA : preferredRealCoordinateJacobian F (0,θ)=preferredSourceJacobian τ p m s θ := by
    simpa only [Complex.ofReal_zero,add_zero] using realSourceChart_jacobian τ δ p m hp hm s 0 θ (by simpa using h)
  have hAn : (preferredRealCoordinateJacobian F (0,θ)).det≠0 := by
    rw [hA]
    exact preferredSourceJacobian_det_ne_zero τ δ p m hp' hm' s θ
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper h.matrix
  have hpiola := preferred_real_coordinate_piola F B 0 θ hF hB hAn
  have hpointEv : ∀ᶠ z : ℝ × (Fin N → ℝ) in 𝓝 (0,θ),
      PreferredFramePoint τ δ p m (s+(z.1:ℂ)) z.2 := by
    have hg : Continuous (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2)) := by fun_prop
    have ht : Tendsto (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2))
        (𝓝 (0,θ)) (𝓝 (s,θ)) := by simpa only [Complex.ofReal_zero,add_zero] using hg.tendsto (0,θ)
    filter_upwards [ht.eventually (hΩ.mem_nhds hz)] with z hz'
    exact hpoint _ hz'
  have hdet : (fun z : ℝ × (Fin N → ℝ) => (preferredRealCoordinateJacobian F z).det)
      =ᶠ[𝓝 (0,θ)] (fun z => coordinateJacobian τ p m (s+(z.1:ℂ)) z.2) := by
    filter_upwards [hpointEv] with z hz'
    rw [realSourceChart_jacobian τ δ p m hp hm s z.1 z.2 hz',coordinateJacobian_eq_shared]
    exact preferredSourceJacobian_det τ δ p m hp' hm' _ _
      hz'.delta_pos hz'.delta_lt hz'.trace_re hz'.trace_cap hz'.angles hz'.upper
  have hvel : (fun x : Fin N → ℝ =>
      (preferredRealCoordinateJacobian F (0,x))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,x)-B x)) =ᶠ[𝓝 θ] angularField anchor τ p m s := by
    have ht : Tendsto (fun x : Fin N → ℝ => ((0:ℝ),x)) (𝓝 θ) (𝓝 (0,θ)) :=
      (continuous_const.prodMk continuous_id).tendsto θ
    filter_upwards [ht.eventually hpointEv] with x hx
    simpa only [Complex.ofReal_zero,add_zero] using realSourceChart_velocity anchor τ δ p m hp hm s 0 x hx
  have hdetParam : (fun u : ℝ => (preferredRealCoordinateJacobian F (u,θ)).det)
      =ᶠ[𝓝 0] (fun u : ℝ => coordinateJacobian τ p m (s+(u:ℂ)) θ) :=
    hdet.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto 0)
  have hdetAngular : (fun x : Fin N → ℝ => (preferredRealCoordinateJacobian F (0,x)).det)
      =ᶠ[𝓝 θ] coordinateJacobian τ p m s := by
    have hh := hdet.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto θ)
    simpa only [Function.comp_def,id_eq,Complex.ofReal_zero,add_zero] using hh
  have hflux (i : Fin N) :
      deriv (fun u : ℝ => ((preferredRealCoordinateJacobian F (0,Function.update θ i u))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,Function.update θ i u)-B (Function.update θ i u))) i*
          (preferredRealCoordinateJacobian F (0,Function.update θ i u)).det) (θ i)=
      deriv (fun u : ℝ => angularField anchor τ p m s (Function.update θ i u) i*
        coordinateJacobian τ p m s (Function.update θ i u)) (θ i) := by
    have ht : Tendsto (fun u : ℝ => Function.update θ i u) (𝓝 (θ i)) (𝓝 θ) := by
      have hh : Continuous (fun u : ℝ => Function.update θ i u) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    apply EventuallyEq.deriv_eq
    filter_upwards [hvel.comp_tendsto ht,hdetAngular.comp_tendsto ht] with u huV huJ
    dsimp only [Function.comp_def] at huV huJ
    rw [huV,huJ]
  have hU (i : Fin N) : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i) :=
    preferred_global_one_sided_joint_analytic s (deformedAngles τ p m θ i) δ
      h.delta_pos h.delta_lt h.trace_re h.trace_im h.trace_cap
      (by simpa only [deformedAngles_re] using (h.angles i).1)
      (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)
  have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
    simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using source_inverseV_ne_zero h i
  have hJ : AnalyticAt ℂ (fun t => coordinateJacobian τ p m t θ) s := by
    simp_rw [coordinateJacobian_eq_shared]
    exact preferredCoordinateJacobian_parameter_analyticAt τ p m s θ h.trace_im h.upper hU hv
  have hJ0 : HasDerivAt (fun t : ℂ => coordinateJacobian τ p m t θ)
      (deriv (fun t : ℂ => coordinateJacobian τ p m t θ) s) (s+(0:ℂ)) := by
    simpa only [add_zero] using hJ.differentiableAt.hasDerivAt
  have hJreal : HasDerivAt (fun u : ℝ => coordinateJacobian τ p m (s+(u:ℂ)) θ)
      (deriv (fun t : ℂ => coordinateJacobian τ p m t θ) s) 0 := by
    simpa only [Function.comp_def,mul_one] using
      (hJ0.comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_add s)).comp_ofReal
  rw [hdetParam.deriv_eq,hJreal.deriv] at hpiola
  simp_rw [hflux] at hpiola
  rw [hA,preferredSourceJacobian_det τ δ p m hp' hm' s θ
    h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper,
    ←coordinateJacobian_eq_shared,
    source_residual_trace anchor τ δ p m hp' hm' s θ h hB] at hpiola
  exact hpiola

end
end IsingBulk.HT22.Anchor
