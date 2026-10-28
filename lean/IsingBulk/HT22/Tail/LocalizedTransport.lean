import IsingBulk.HT22.Tail.CollisionBounds

/-! Arbitrary smooth localized seeds use the same actual F001 field. The
weight is placed inside the recurrence, so its derivatives are retained. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def scalarIterate {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => A
  | j+1 => regularTransportStep τ p m (scalarIterate τ p m A j)

def densityIterate {N : ℕ} (σ : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => fun t x => coordinateJacobian τ p m t x*sourceSignedResolvent σ τ p m t x*A t x
  | j+1 => preferredTransportStep (angularField τ p m) (densityIterate σ τ p m A j)

theorem scalarIterate_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => scalarIterate τ p m A j z.1 z.2) Ω := by
  obtain ⟨hV,hD⟩ := source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR
  induction j with
  | zero => exact hA
  | succ j ih => exact regularTransportStep_mixed τ p m Ω hΩ hV hD _ ih

theorem densityIterate_factorization {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    densityIterate σ τ p m A j s θ=coordinateJacobian τ p m s θ*
      sourceSignedResolvent σ τ p m s θ*scalarIterate τ p m A j s θ := by
  induction j generalizing s θ with
  | zero => rfl
  | succ j ih =>
    have he : (fun z : ℂ × (Fin N → ℝ) => densityIterate σ τ p m A j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] (fun z => coordinateJacobian τ p m z.1 z.2*
          sourceSignedResolvent σ τ p m z.1 z.2*scalarIterate τ p m A j z.1 z.2) := by
      filter_upwards [hΩ.mem_nhds hz] with z hz'
      exact ih z.1 z.2 hz'
    have hs := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s)
    have hx (i : Fin N) : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      have hh : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    have ht : preferredTransportStep (angularField τ p m) (densityIterate σ τ p m A j) s θ=
        preferredTransportStep (angularField τ p m)
          (fun t x => coordinateJacobian τ p m t x*sourceSignedResolvent σ τ p m t x*
            scalarIterate τ p m A j t x) s θ := by
      unfold preferredTransportStep preferredAngularDivergence
      simp only [Function.comp_def,id_eq] at hs
      rw [hs.deriv_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply EventuallyEq.deriv_eq
      filter_upwards [he.comp_tendsto (hx i)] with x hh
      change densityIterate σ τ p m A j s (Function.update θ i x)=_ at hh
      rw [hh]
      rfl
    change preferredTransportStep (angularField τ p m) (densityIterate σ τ p m A j) s θ=_
    rw [ht,physical_transport_factorization hN σ hσ τ δ p m hp hm Ω hΩ hpoint hR _
      (scalarIterate_mixed τ δ p m hp hm Ω hΩ hpoint hR A hA j) s θ hz]
    rfl

end
end IsingBulk.HT22.Tail
