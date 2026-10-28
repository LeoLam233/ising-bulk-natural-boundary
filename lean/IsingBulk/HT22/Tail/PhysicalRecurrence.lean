import IsingBulk.HT22.Tail.PhaseFreeze
import IsingBulk.HT22.Tail.FrameCalculus

/-! Equality of the literal physical derivative-minus-divergence recurrence
with the new regular scalar recurrence, at every finite derivative order.
No smooth real weight is analytically continued. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem coordinateJacobian_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => coordinateJacobian τ p m z.1 z.2) Ω := by
  intro z hz
  have h := hpoint z hz
  have hU (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i) :=
    preferred_global_one_sided_joint_analytic z.1 (deformedAngles τ p m z.2 i) δ
      h.delta_pos h.delta_lt h.trace_re h.trace_im h.trace_cap
      (by simpa only [deformedAngles_re] using (h.angles i).1)
      (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)
  have hv (i : Fin N) : preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)≠0 := by
    simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using source_inverseV_ne_zero h i
  simp_rw [coordinateJacobian_eq_shared]
  exact ⟨preferredCoordinateJacobian_contDiffAt τ p m hp hm z.1 z.2 h.trace_im h.upper hU hv,
    (preferredCoordinateJacobian_parameter_analyticAt τ p m z.1 z.2 h.trace_im h.upper hU hv).differentiableAt⟩

theorem sourceSignedResolvent_mixed {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => sourceSignedResolvent σ τ p m z.1 z.2) Ω := by
  intro z hz
  have h := hpoint z hz
  have ha := signedPhaseResolvent_analyticAt_source hN σ hσ τ p m z.1 z.2 h.upper
  constructor
  · exact (ha.contDiffAt.restrict_scalars ℝ).comp z
      (preferredSourcePhaseSum_contDiffAt τ p m hp hm z.1 z.2 h.trace_im h.upper)
  · exact ha.differentiableAt.comp z.1
      (preferredSourcePhaseSum_parameter_analyticAt τ p m z.1 z.2 h.trace_im h.upper).differentiableAt

theorem sourceBorderedDet_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => (sourceBorderedKernel τ p m z.1 z.2).det) Ω := by
  apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
    (fun z => (regularBorderedKernel z.1 z.2).det)
  intro z hz
  have h := hpoint z hz
  have hK := source_regularBorderedKernel_analyticAt τ δ p m z.1 z.2
    h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper
  simp only [Matrix.det_apply']
  exact Finset.univ.analyticAt_fun_sum (fun e _ => analyticAt_const.mul
    (Finset.univ.analyticAt_fun_prod (fun i _ =>
      analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hK (e i)) i)))

theorem regularTransportedScalar_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) : PreferredMixedSmoothOn (fun z => regularTransportedScalar τ η p m r j z.1 z.2) Ω := by
  obtain ⟨hV,hD⟩ := source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR
  induction j with
  | zero =>
    exact (regularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint).mul
      (sourceBorderedDet_mixed τ δ p m hp hm Ω hpoint)
  | succ j ih => exact regularTransportStep_mixed τ p m Ω hΩ hV hD _ ih

theorem physical_transport_factorization {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (G : ℂ → (Fin N → ℝ) → ℂ)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredTransportStep (angularField τ p m)
      (fun t x => coordinateJacobian τ p m t x*sourceSignedResolvent σ τ p m t x*G t x) s θ=
      coordinateJacobian τ p m s θ*sourceSignedResolvent σ τ p m s θ*
        regularTransportStep τ p m G s θ := by
  have hJ := coordinateJacobian_mixed τ δ p m hp hm Ω hpoint (s,θ) hz
  have hH := sourceSignedResolvent_mixed hN σ hσ τ δ p m hp hm Ω hpoint (s,θ) hz
  have hV := (source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR).1
  have hx {F : ℂ × (Fin N → ℝ) → ℂ} (hh : ContDiffAt ℝ ∞ F (s,θ)) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (s,Function.update θ i x)) (θ i) :=
    preferredMixed_coordinate_differentiable (fun t x => F (t,x)) s θ hh i
  rw [preferredTransportStep_factored _ _ _ _ s θ (regularDivergence τ p m s θ)
    hJ.2 hH.2 (hG (s,θ) hz).2 (hx hJ.1) (hx hH.1) (hx (hG (s,θ) hz).1)
    (fun i => hx (hV i (s,θ) hz).1 i)
    (coordinateJacobian_piola τ δ p m hp hm Ω hΩ hpoint hR s θ hz)
    (sourceSignedResolvent_material_freeze hN σ hσ τ δ p m
      (hp.differentiable (by simp)) (hm.differentiable (by simp)) s θ (hpoint (s,θ) hz) (hR (s,θ) hz))]
  rw [regularTransportStep_eq]

/-- All physical descendants equal the reconstructed density, not by
definition but by the source Piola equation and frozen signed resolvent. -/
theorem transportedDensity_eq_reconstructed {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    transportedDensity σ τ η p m r j s θ=reconstructedDensity σ τ η p m r j s θ := by
  induction j generalizing s θ with
  | zero =>
    have h := hpoint (s,θ) hz
    exact physicalSeed_eq_reconstructed_zero σ τ δ η p m r s θ
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper
  | succ j ih =>
    have he : (fun z : ℂ × (Fin N → ℝ) => transportedDensity σ τ η p m r j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] (fun z => coordinateJacobian τ p m z.1 z.2*
          sourceSignedResolvent σ τ p m z.1 z.2*regularTransportedScalar τ η p m r j z.1 z.2) := by
      filter_upwards [hΩ.mem_nhds hz] with z hz'
      rw [ih z.1 z.2 hz',reconstructedDensity_eq_source σ τ δ η p m r j z.1 z.2 (hpoint z hz')]
    have hs := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s)
    have hx (i : Fin N) : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      have hh : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    have ht : preferredTransportStep (angularField τ p m) (transportedDensity σ τ η p m r j) s θ=
        preferredTransportStep (angularField τ p m)
          (fun t x => coordinateJacobian τ p m t x*sourceSignedResolvent σ τ p m t x*
            regularTransportedScalar τ η p m r j t x) s θ := by
      unfold preferredTransportStep preferredAngularDivergence
      simp only [Function.comp_def,id_eq] at hs
      rw [hs.deriv_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply EventuallyEq.deriv_eq
      filter_upwards [he.comp_tendsto (hx i)] with x hh
      change transportedDensity σ τ η p m r j s (Function.update θ i x)=_ at hh
      rw [hh]
      rfl
    change preferredTransportStep (angularField τ p m) (transportedDensity σ τ η p m r j) s θ=_
    rw [ht,physical_transport_factorization hN σ hσ τ δ p m hp hm Ω hΩ hpoint hR _
      (regularTransportedScalar_mixed τ δ η p m r hη hp hm hr Ω hΩ hpoint hR j) s θ hz,
      reconstructedDensity_eq_source σ τ δ η p m r (j+1) s θ (hpoint (s,θ) hz)]
    rfl

end
end IsingBulk.HT22.Tail
