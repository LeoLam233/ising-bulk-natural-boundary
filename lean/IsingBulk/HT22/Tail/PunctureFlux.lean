import IsingBulk.HT22.Tail.PhysicalRecurrence
import IsingBulk.Preferred22.EqualityCutoff

/-! Genuine puncture current for the new physical transport. The cutoff is
real, differentiated before any shell partition, and includes the original
occupancy-dependent angular field. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def punctureFlux {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (R : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i,(preferredEqualityCutoffPartial R θ i:ℂ)*angularField τ p m s θ i*
    transportedDensity σ τ η p m r j s θ

theorem punctureFlux_zero_outside {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) {R : ℝ} (hR : 0<R) (θ : Fin N → ℝ)
    (hd : R<preferredAngularDiameter θ) : punctureFlux σ τ η p m r j s R θ=0 := by
  unfold punctureFlux
  apply Finset.sum_eq_zero
  intro i _
  rw [preferredEqualityCutoffPartial_zero_of_diameter_lt hR θ i hd,
    Complex.ofReal_zero,zero_mul,zero_mul]

/-- The actual current costs two powers of the puncture radius, but no
partial-collision pole. A true primitive angular-field bound is the only
field hypothesis; no descendant bound is assumed. -/
theorem punctureFlux_pointwise :
    ∃ A : ℝ,0<A ∧ ∀ N : ℕ,∀ σ : ℂ,∀ τ R C : ℝ,0<R → 0<C →
      ∀ η p m r : ℝ → ℝ,∀ j : ℕ,∀ s : ℂ,∀ θ : Fin N → ℝ,
      (0<preferredAngularDiameter θ → ∀ i,
        ‖angularField τ p m s θ i‖≤C*(N:ℝ)^2/preferredAngularDiameter θ) →
      ‖punctureFlux σ τ η p m r j s R θ‖≤A*C*(N:ℝ)^5/R^2*
        ‖transportedDensity σ τ η p m r j s θ‖ := by
  obtain ⟨A,hA,hpartial⟩ := preferredEqualityCutoffPartial_bound
  refine ⟨A,hA,?_⟩
  intro N σ τ R C hR hC η p m r j s θ hfield
  let P := transportedDensity σ τ η p m r j s θ
  have hterm (i : Fin N) :
      ‖(preferredEqualityCutoffPartial R θ i:ℂ)*angularField τ p m s θ i*P‖≤
      A*C*(N:ℝ)^4/R^2*‖P‖ := by
    by_cases hd : 0<preferredAngularDiameter θ
    · rw [norm_mul,norm_mul,Complex.norm_real]
      have hh := mul_le_mul (hpartial N R hR θ i) (hfield hd i) (norm_nonneg _) (by positivity)
      calc
        _ ≤ ((A*(N:ℝ)^2*preferredAngularDiameter θ/R^2)*(C*(N:ℝ)^2/preferredAngularDiameter θ))*‖P‖ :=
          mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _ = _ := by field_simp [hd.ne']
    · have hz : preferredAngularDiameter θ=0 := le_antisymm (le_of_not_gt hd) Metric.diam_nonneg
      have hh := hpartial N R hR θ i
      rw [hz,mul_zero,zero_div] at hh
      have hp : preferredEqualityCutoffPartial R θ i=0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      rw [hp,Complex.ofReal_zero,zero_mul,zero_mul,norm_zero]
      positivity
  unfold punctureFlux
  calc
    _ ≤ ∑ i : Fin N,‖(preferredEqualityCutoffPartial R θ i:ℂ)*angularField τ p m s θ i*P‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N,A*C*(N:ℝ)^4/R^2*‖P‖ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem transportedDensity_mixed {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => transportedDensity σ τ η p m r j z.1 z.2) Ω := by
  have hJ := coordinateJacobian_mixed τ δ p m hp hm Ω hpoint
  have hH := sourceSignedResolvent_mixed hN σ hσ τ δ p m hp hm Ω hpoint
  have hG := regularTransportedScalar_mixed τ δ η p m r hη hp hm hr Ω hΩ hpoint hR j
  apply ((hJ.mul hH).mul hG).congr hΩ
  intro z hz
  rw [transportedDensity_eq_reconstructed hN σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint hR j z.1 z.2 hz,
    reconstructedDensity_eq_source σ τ δ η p m r j z.1 z.2 (hpoint z hz)]

/-- Literal weighted transport before integration, on the actual regular
chart. In particular the current is not differentiated after dyadic shell
localization. -/
theorem punctured_transport_identity {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (R : ℝ) :
    preferredTransportStep (angularField τ p m)
      (fun t x => (preferredEqualityCutoff R x:ℂ)*transportedDensity σ τ η p m r j t x) s θ=
      (preferredEqualityCutoff R θ:ℂ)*transportedDensity σ τ η p m r (j+1) s θ-
        punctureFlux σ τ η p m r j s R θ := by
  have hP := transportedDensity_mixed hN σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint hR j
  have hV := (source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR).1
  apply preferredTransportStep_weighted (angularField τ p m) (preferredEqualityCutoff R)
    (transportedDensity σ τ η p m r j) s θ (preferredEqualityCutoffPartial R θ) (hP _ hz).2
  · intro i
    have hc := (preferredEqualityCutoff_smooth (N:=N) R).comp (contDiff_update ∞ θ i)
    exact ((hc.differentiable (by simp)).differentiableAt).hasDerivAt
  · intro i
    exact preferredMixed_coordinate_differentiable
      (fun t x => angularField τ p m t x i*transportedDensity σ τ η p m r j t x)
      s θ (((hV i).mul hP) _ hz).1 i

end
end IsingBulk.HT22.Tail
