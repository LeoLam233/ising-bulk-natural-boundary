import IsingBulk.HT22.Anchor.Generator
import IsingBulk.HT22.Anchor.PhysicalSeed
import IsingBulk.Preferred22.PhysicalDensityRegularity
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry IsingBulk.HT22.Tail Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def regularSeed {N : ℕ} (anchor : Fin N) (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight (.anchor anchor) η p m r θ:ℂ)*
    fixedAmplitude σ t (sourceCoordinate τ p m t θ)

def regularTransportedScalar {N : ℕ} (anchor : Fin N) (σ : ℂ) (τ : ℝ)
    (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => regularSeed anchor σ τ η p m r
  | j+1 => regularTransportStep anchor τ p m (regularTransportedScalar anchor σ τ η p m r j)

def transportedDensity {N : ℕ} (anchor : Fin N) (σ : ℂ) (τ : ℝ)
    (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => fun t θ => physicalSeed σ τ p m
      (preferredCellWeight (.anchor anchor) η p m r θ) t θ
  | j+1 => preferredTransportStep (angularField anchor τ p m) (transportedDensity anchor σ τ η p m r j)

theorem regularSeed_mixed {N : ℕ} (hN : 0<N) (anchor : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => regularSeed anchor σ τ η p m r z.1 z.2) Ω := by
  have hbody := (preferred_regular_factors_mixed τ δ p m hp hm Ω hpoint).2
  have hw : PreferredMixedSmoothOn
      (fun z : ℂ × (Fin N → ℝ) => (preferredCellWeight (.anchor anchor) η p m r z.2:ℂ)) Ω := by
    intro z _
    exact ⟨(Complex.ofRealCLM.contDiff.comp
      ((preferredCellWeight_contDiff (.anchor anchor) η p m r hη hp hm hr).comp contDiff_snd)).contDiffAt,
      differentiableAt_const (𝕜:=ℂ) (x:=z.1) (preferredCellWeight (.anchor anchor) η p m r z.2:ℂ)⟩
  have hb : PreferredMixedSmoothOn
      (fun z : ℂ × (Fin N → ℝ) => (∏ i,preferredRegularOneBody z.1
        (preferredSourceCoordinate τ p m z.1 z.2 i))/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))) Ω := by
    intro z hz
    exact ⟨(contDiffAt_prod (fun i _ => (hbody i z hz).1)).div_const _,
      (DifferentiableAt.fun_finsetProd (fun i _ => (hbody i z hz).2)).div_const _⟩
  have hh := ((hw.mul (sourceSignedResolvent_mixed hN σ hσ τ δ p m hp hm Ω hpoint)).mul
    (sourceBorderedDet_mixed τ δ p m hp hm Ω hpoint)).mul hb
  apply hh.congr hΩ
  intro z hz
  unfold regularSeed fixedAmplitude
  rw [regularProductPhase_eq_source τ δ p m z.1 z.2 (hpoint z hz)]
  simp only [sourceSignedResolvent,signedPhaseResolvent,preferredSourceProductPhase,
    sourceBorderedKernel,regularOneBody_moving_adapter,sourceCoordinate_moving_adapter]
  ring

theorem regularTransportedScalar_mixed {N : ℕ} (hN : 0<N) (anchor : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => regularTransportedScalar anchor σ τ η p m r j z.1 z.2) Ω := by
  obtain ⟨hV,hD⟩ := source_generator_mixed anchor τ δ p m hp hm Ω hΩ hpoint
  induction j with
  | zero => exact regularSeed_mixed hN anchor σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint
  | succ j ih => exact regularTransportStep_mixed anchor τ p m Ω hΩ hV hD _ ih
theorem transportedDensity_eq_reconstructed {N : ℕ} (hN : 0<N) (anchor : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    transportedDensity anchor σ τ η p m r j s θ=coordinateJacobian τ p m s θ*regularTransportedScalar anchor σ τ η p m r j s θ := by
  induction j generalizing s θ with
  | zero =>
    have h := hpoint (s,θ) hz
    change physicalSeed σ τ p m (preferredCellWeight (.anchor anchor) η p m r θ) s θ=_
    rw [physicalSeed_eq_fixedAmplitude σ τ δ p m _ s θ
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper]
    unfold regularTransportedScalar regularSeed
    ring
  | succ j ih =>
    have he : (fun z : ℂ × (Fin N → ℝ) => transportedDensity anchor σ τ η p m r j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] (fun z => coordinateJacobian τ p m z.1 z.2*
          regularTransportedScalar anchor σ τ η p m r j z.1 z.2) := by
      filter_upwards [hΩ.mem_nhds hz] with z hz'
      exact ih z.1 z.2 hz'
    have hs := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s)
    have hx (i : Fin N) : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      have hh : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    have ht : preferredTransportStep (angularField anchor τ p m) (transportedDensity anchor σ τ η p m r j) s θ=
        preferredTransportStep (angularField anchor τ p m)
          (fun t x => coordinateJacobian τ p m t x*
            regularTransportedScalar anchor σ τ η p m r j t x) s θ := by
      unfold preferredTransportStep preferredAngularDivergence
      simp only [Function.comp_def,id_eq] at hs
      rw [hs.deriv_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply EventuallyEq.deriv_eq
      filter_upwards [he.comp_tendsto (hx i)] with x hh
      change transportedDensity anchor σ τ η p m r j s (Function.update θ i x)=_ at hh
      rw [hh]
      rfl
    change preferredTransportStep (angularField anchor τ p m) (transportedDensity anchor σ τ η p m r j) s θ=_
    rw [ht,physical_transport_factorization anchor τ δ p m hp hm Ω hΩ hpoint _
      (regularTransportedScalar_mixed hN anchor σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint j) s θ hz]
    rfl

end
end IsingBulk.HT22.Anchor
