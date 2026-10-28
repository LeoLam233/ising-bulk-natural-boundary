import IsingBulk.HT22.Tail.LocalizedTransport

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def localizedSeed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (W : (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  W θ*regularSeed τ η p m r s θ

def localizedPhysicalDensity {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (W : (Fin N → ℝ) → ℂ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => fun s θ => W θ*physicalSeed σ τ η p m r s θ
  | j+1 => preferredTransportStep (angularField τ p m) (localizedPhysicalDensity σ τ η p m r W j)

theorem localizedSeed_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) :
    PreferredMixedSmoothOn (fun z => localizedSeed τ η p m r W z.1 z.2) Ω := by
  have hw : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => W z.2) Ω :=
    fun z _ => ⟨hW.contDiffAt.comp z contDiffAt_snd,differentiableAt_const (W z.2)⟩
  exact hw.mul (regularTransportedScalar_mixed τ δ η p m r hη hp hm hr Ω hΩ hpoint hR 0)

theorem localizedPhysicalDensity_factorization {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    localizedPhysicalDensity σ τ η p m r W j s θ=coordinateJacobian τ p m s θ*
      sourceSignedResolvent σ τ p m s θ*scalarIterate τ p m (localizedSeed τ η p m r W) j s θ := by
  have hA := localizedSeed_mixed τ δ η p m r hη hp hm hr W hW Ω hΩ hpoint hR
  induction j generalizing s θ with
  | zero =>
    have hh := transportedDensity_eq_reconstructed hN σ hσ τ δ η p m r hη hp hm hr
      Ω hΩ hpoint hR 0 s θ hz
    rw [reconstructedDensity_eq_source σ τ δ η p m r 0 s θ (hpoint (s,θ) hz)] at hh
    change W θ*physicalSeed σ τ η p m r s θ=_
    change physicalSeed σ τ η p m r s θ=_ at hh
    rw [hh]
    change W θ*(_*_*regularSeed τ η p m r s θ)=_*_*(W θ*regularSeed τ η p m r s θ)
    ring
  | succ j ih =>
    have he : (fun z : ℂ × (Fin N → ℝ) => localizedPhysicalDensity σ τ η p m r W j z.1 z.2)
        =ᶠ[𝓝 (s,θ)] (fun z => coordinateJacobian τ p m z.1 z.2*
          sourceSignedResolvent σ τ p m z.1 z.2*scalarIterate τ p m (localizedSeed τ η p m r W) j z.1 z.2) := by
      filter_upwards [hΩ.mem_nhds hz] with z hz'
      exact ih z.1 z.2 hz'
    have hs := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s)
    have hx (i : Fin N) : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      have hh : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    change preferredTransportStep (angularField τ p m) (localizedPhysicalDensity σ τ η p m r W j) s θ=_
    have ht : preferredTransportStep (angularField τ p m) (localizedPhysicalDensity σ τ η p m r W j) s θ=
        preferredTransportStep (angularField τ p m)
          (fun t x => coordinateJacobian τ p m t x*sourceSignedResolvent σ τ p m t x*
            scalarIterate τ p m (localizedSeed τ η p m r W) j t x) s θ := by
      unfold preferredTransportStep preferredAngularDivergence
      simp only [Function.comp_def,id_eq] at hs
      rw [hs.deriv_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply EventuallyEq.deriv_eq
      filter_upwards [he.comp_tendsto (hx i)] with x hh
      change localizedPhysicalDensity σ τ η p m r W j s (Function.update θ i x)=_ at hh
      rw [hh]
      rfl
    rw [ht,physical_transport_factorization hN σ hσ τ δ p m hp hm Ω hΩ hpoint hR _
      (scalarIterate_mixed τ δ p m hp hm Ω hΩ hpoint hR _ hA j) s θ hz]
    rfl

end
end IsingBulk.HT22.Tail
