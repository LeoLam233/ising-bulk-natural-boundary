import IsingBulk.AnisoF002.C03.IsotropicCurrentNeighborhood

/-!
# The actual current on the original constrained real angles

The angular velocity is tangent on a neighborhood, not merely at one
point. Consequently the exact scalar current has the constrained real
divergence after any anchor angle is eliminated. This is a differential
identity; puncture flux and integration estimates are separate work.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric Filter

/-- The actual physical current uses the original constrained real
directions `e_i - e_anchor`. The regular field, velocity, determinant,
and all derivatives are the constructed ones. -/
theorem exists_actual_right_constrained_current (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j → ∀ anchor : Fin N,
        ∀ b : (ℂ × (Fin N → ℝ)) → ℂ, DifferentiableAt ℝ b (s, θ) →
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y * b y)
              actualTimeDirection (s, θ) -
            (∑ k ∈ Finset.univ.erase anchor,
              scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
                actualCoordinateDeterminant η τ ξ y * b y)
                (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) *
            (scalarRegularParameterDerivative (actualPhysicalCoordinate η τ ξ)
                actualAngularDirection actualTimeDirection b (s, θ) +
              (∑ k, actualCovarianceRegularField η τ ξ k (s, θ) *
                scalarRegularFrameDerivative (actualPhysicalCoordinate η τ ξ)
                  actualAngularDirection b k (s, θ)) +
              (∑ k, scalarRegularFrameDerivative (actualPhysicalCoordinate η τ ξ)
                actualAngularDirection (actualCovarianceRegularField η τ ξ k) k (s, θ)) * b (s, θ)) := by
  obtain ⟨r, hr, hdata⟩ := exists_actual_right_current_data S η hS hη
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : δ < r := half_lt_self hr
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor b hb
  have hτr : τ ∈ Icc 0 r := ⟨hτ.1, hτ.2.trans hδr.le⟩
  have hθr : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r) r :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hδr.le⟩
  obtain ⟨hχ, hdet, hB, hV, _⟩ := hdata N hN s hs (hsnear.trans hδr) τ hτr ξ hξ θ hθr i j hij
  have hJ : DifferentiableAt ℝ (actualCoordinateDeterminant η τ ξ) (s, θ) :=
    scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ) actualAngularDirection (s, θ) hχ
  have hsim : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.1.im) (s, θ) := by fun_prop
  have hdist : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => dist q.1 (S : ℂ)) (s, θ) := by fun_prop
  have hangle (k : Fin N) : ∀ᶠ q : ℂ × (Fin N → ℝ) in 𝓝 (s, θ),
      q.2 k ∈ Icc (-rightBranchEndpoint S - r) r := by
    have hk : θ k ∈ Ioo (-rightBranchEndpoint S - r) r :=
      ⟨by linarith [(hθ k).1], (hθ k).2.trans_lt hδr⟩
    have hc : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 k) (s, θ) := by fun_prop
    exact (hc.eventually (isOpen_Ioo.mem_nhds hk)).mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hdiff : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 i - q.2 j) (s, θ) := by fun_prop
  have htangent : (fun q : ℂ × (Fin N → ℝ) =>
      ∑ k, actualCovarianceAngularVelocity η τ ξ k q) =ᶠ[𝓝 (s, θ)] (fun _ => 0) := by
    filter_upwards [hsim.eventually (Ioi_mem_nhds hs),
      hdist.eventually (Iio_mem_nhds (hsnear.trans hδr)),
      Filter.eventually_all.mpr hangle, hdiff.eventually_ne (sub_ne_zero.mpr hij)] with q hqs hqd hqθ hqij
    exact (hdata N hN q.1 hqs hqd τ hτr ξ hξ q.2 hqθ i j (sub_ne_zero.mp hqij)).2.2.2.2
  have hFtangent : (fun q : ℂ × (Fin N → ℝ) => ∑ k,
      actualCovarianceAngularVelocity η τ ξ k q * actualCoordinateDeterminant η τ ξ q * b q)
      =ᶠ[𝓝 (s, θ)] (fun _ => 0) := by
    filter_upwards [htangent] with q hq
    rw [← Finset.sum_mul, ← Finset.sum_mul, hq, zero_mul, zero_mul]
  have hdiv := tangent_current_constrained_divergence
    (fun k q => actualCovarianceAngularVelocity η τ ξ k q * actualCoordinateDeterminant η τ ξ q * b q)
    actualAngularDirection (s, θ) anchor (fun k => ((hV k).mul hJ).mul hb) hFtangent
  rw [hdiv]
  exact exact_constructed_regular_current (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ) b hχ hB hb hdet

end IsingBulk.AnisoF002.Isotropic
