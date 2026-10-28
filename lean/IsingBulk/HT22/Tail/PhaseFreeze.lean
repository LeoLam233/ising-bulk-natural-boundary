import IsingBulk.HT22.Tail.SourcePiola

/-! Actual signed physical phase freezing for the mixed covariance field.
Both signs retain exactly one simple product denominator. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def signedPhaseResolvent (σ z : ℂ) : ℂ :=
  (1+σ*Complex.exp (-Complex.I*z))/(1-σ*Complex.exp (-Complex.I*z))

def sourceSignedResolvent {N : ℕ} (σ : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  signedPhaseResolvent σ (preferredSourcePhaseSum τ p m s θ)

theorem sourcePhase_parameter_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) (i : Fin N) :
    HasDerivAt (fun t : ℂ => preferredSourcePhase τ p m t θ i)
      (-inverseT s (sourceCoordinate τ p m s θ i)/inverseV s (sourceCoordinate τ p m s θ i)) s := by
  have hh := (sourceCoordinate_parameter_hasDerivAt τ δ p m s θ h i).sub_const
    (deformedAngles τ p m θ i)
  convert hh using 1
  funext t
  unfold sourceCoordinate sumCoordinate physicalPhase preferredSourcePhase
  ring

theorem sourcePhase_angular_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) (i j : Fin N) :
    HasDerivAt (fun x : ℝ => preferredSourcePhase τ p m s (Function.update θ j x) i)
      (((inverseV s (sourceCoordinate τ p m s θ i))⁻¹-1)*preferredContourMatrix τ p m θ i j) (θ j) := by
  simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using
    preferredSourcePhase_angular_hasDerivAt τ δ p m hp hm s θ i j
      h.delta_pos h.delta_lt h.trace_re h.trace_cap (h.angles i) (h.upper i)

theorem sourcePhaseSum_material_freeze {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ)
    (hR : sourceCovariance s (sourceCoordinate τ p m s θ)≠0) :
    deriv (fun t : ℂ => preferredSourcePhaseSum τ p m t θ) s-
      (∑ j, angularField τ p m s θ j*
        deriv (fun x : ℝ => preferredSourcePhaseSum τ p m s (Function.update θ j x)) (θ j))=0 := by
  have hs := (HasDerivAt.sum (u:=Finset.univ)
    (fun i _ => sourcePhase_parameter_hasDerivAt τ δ p m s θ h i)).deriv
  have hx (j : Fin N) := (HasDerivAt.sum (u:=Finset.univ)
    (fun i _ => sourcePhase_angular_hasDerivAt τ δ p m hp hm s θ h i j)).deriv
  simp only [preferredSourcePhaseSum,Finset.sum_fn] at ⊢ hs hx
  rw [hs]
  simp_rw [hx]
  exact mixedAngularField_phase_algebra (preferredContourMatrix τ p m θ)
    (fun i => regularInverse s (sourceCoordinate τ p m s θ i))
    (fun i => inverseV s (sourceCoordinate τ p m s θ i))
    (fun i => inverseT s (sourceCoordinate τ p m s θ i)) h.matrix
    (source_inverseV_ne_zero h) hR

theorem signedPhaseResolvent_analyticAt_source {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (signedPhaseResolvent σ) (preferredSourcePhaseSum τ p m s θ) := by
  have hden : 1-σ*Complex.exp (-Complex.I*preferredSourcePhaseSum τ p m s θ)≠0 := by
    intro he
    have hz : σ*preferredSourceProductPhase τ p m s θ=1 := (sub_eq_zero.mp he).symm
    have hn : ‖σ*preferredSourceProductPhase τ p m s θ‖<1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans_lt
        (by simpa only [one_mul] using preferredSourceProductPhase_norm_lt_one hN τ p m s θ hW)
    rw [hz,norm_one] at hn
    exact (lt_irrefl 1) hn
  have he : AnalyticAt ℂ (fun z : ℂ => σ*Complex.exp (-Complex.I*z)) (preferredSourcePhaseSum τ p m s θ) :=
    analyticAt_const.mul (analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id))
  exact (analyticAt_const.add he).div (analyticAt_const.sub he) hden

theorem sourceSignedResolvent_material_freeze {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ)
    (hR : sourceCovariance s (sourceCoordinate τ p m s θ)≠0) :
    deriv (fun t : ℂ => sourceSignedResolvent σ τ p m t θ) s-
      (∑ j, angularField τ p m s θ j*
        deriv (fun x : ℝ => sourceSignedResolvent σ τ p m s (Function.update θ j x)) (θ j))=0 := by
  have hs : DifferentiableAt ℂ (fun t => preferredSourcePhaseSum τ p m t θ) s :=
    (preferredSourcePhaseSum_parameter_analyticAt τ p m s θ h.trace_im h.upper).differentiableAt
  have hx (j : Fin N) : DifferentiableAt ℝ
      (fun x => preferredSourcePhaseSum τ p m s (Function.update θ j x)) (θ j) := by
    simpa only [preferredSourcePhaseSum,Finset.sum_fn] using
      (HasDerivAt.sum (u:=Finset.univ)
        (fun i _ => sourcePhase_angular_hasDerivAt τ δ p m hp hm s θ h i j)).differentiableAt
  unfold sourceSignedResolvent
  rw [preferred_material_chain_rule _ _ _ s θ hs hx
    (signedPhaseResolvent_analyticAt_source hN σ hσ τ p m s θ h.upper).differentiableAt,
    sourcePhaseSum_material_freeze τ δ p m hp hm s θ h hR,mul_zero]

theorem regularProductPhase_eq_source {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) :
    regularProductPhase s (sourceCoordinate τ p m s θ)=preferredSourceProductPhase τ p m s θ := by
  unfold regularProductPhase preferredSourceProductPhase preferredSourcePhaseSum
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact global_one_sided_phase s (deformedAngles τ p m θ i) δ
    h.delta_pos h.delta_lt h.trace_re h.trace_cap
    (by simpa only [deformedAngles_re] using (h.angles i).1)
    (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)

theorem reconstructedDensity_eq_source {N : ℕ} (σ : ℂ) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) :
    reconstructedDensity σ τ η p m r j s θ=
      coordinateJacobian τ p m s θ*sourceSignedResolvent σ τ p m s θ*
        regularTransportedScalar τ η p m r j s θ := by
  unfold reconstructedDensity
  rw [regularProductPhase_eq_source τ δ p m s θ h]
  rfl

end
end IsingBulk.HT22.Tail
