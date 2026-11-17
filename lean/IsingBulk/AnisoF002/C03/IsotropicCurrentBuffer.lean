import IsingBulk.AnisoF002.C03.IsotropicCurrentBufferData
import IsingBulk.AnisoF002.C03.IsotropicInitialAmplitude

/-!
# Complete actual constrained currents with independent angular geometry

The smooth cutoff width is selected after an angular buffer. Every
transport order uses the same later deformation/parameter radius,
the genuine physical kernel, determinant, and full normalized amplitude.
Tangency holds on a neighborhood, so the divergence is exactly the
original constrained real divergence after any anchor is eliminated.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Metric Filter

theorem exists_actual_iterated_constrained_current_buffer (S : ℝ)
    (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        ∀ i j, θ i ≠ θ j → ∀ anchor : Fin N,
        ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ∀ b : (ℂ × (Fin N → ℝ)) → ℂ, ContDiffAt ℝ ∞ b (s, θ) → ∀ n : ℕ,
          ContDiffAt ℝ ∞ (actualTransportDescendant η τ ξ b n) (s, θ) ∧
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y *
              (actualSignedProductKernel σ η τ ξ y * actualTransportDescendant η τ ξ b n y))
                actualTimeDirection (s, θ) -
            (∑ k ∈ Finset.univ.erase anchor,
              scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
                actualCoordinateDeterminant η τ ξ y *
                  (actualSignedProductKernel σ η τ ξ y * actualTransportDescendant η τ ξ b n y))
                (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) * actualSignedProductKernel σ η τ ξ (s, θ) *
            actualTransportDescendant η τ ξ b (n + 1) (s, θ) := by
  obtain ⟨β₀, hβ₀, hβ₀1, hdata⟩ := exists_actual_right_smooth_current_buffer S hS
  let β := β₀ / 2
  have hβ : 0 < β := half_pos hβ₀
  have hb0 : β < β₀ := half_lt_self hβ₀
  refine ⟨β, hβ, hb0.le.trans hβ₀1, ?_⟩
  intro η hη
  obtain ⟨r, hr, _, hd⟩ := hdata η hη
  let δ := min β (r / 2)
  have hδ : 0 < δ := lt_min hβ (half_pos hr)
  have hdβ : δ ≤ β := min_le_left _ _
  have hdr : δ < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor σ hσ b hb n
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hτr : τ ∈ Icc 0 r := ⟨hτ.1, hτ.2.trans hdr.le⟩
  have hθr : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β₀) β₀ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb0.le⟩
  obtain ⟨hχ, hdet, hB, hV, htan⟩ := hd N hN s hs (hsnear.trans hdr) τ hτr ξ hξ θ hθr i j hij
  have hχ₂ (k : Fin N) : ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ k) (s, θ) :=
    (hχ k).of_le (by simp)
  have hBd (k : Fin N) : DifferentiableAt ℝ (actualCovarianceRegularField η τ ξ k) (s, θ) :=
    (hB k).differentiableAt (by simp)
  have hn := regularTransportDescendant_contDiffAt (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ)
    b hχ hB hb hdet n
  refine ⟨hn, ?_⟩
  have hnd : DifferentiableAt ℝ (actualTransportDescendant η τ ξ b n) (s, θ) :=
    hn.differentiableAt (by simp)
  obtain ⟨hK, hfreeze⟩ := actualSignedProductKernel_transport σ hσ η τ ξ hη hτ.1 hξ.1
    (s, θ) hs hχ₂ hdet htan
  have hJ : DifferentiableAt ℝ (actualCoordinateDeterminant η τ ξ) (s, θ) :=
    scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ) actualAngularDirection (s, θ) hχ₂
  have hsim : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.1.im) (s, θ) := by fun_prop
  have hdist : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => dist q.1 (S : ℂ)) (s, θ) := by fun_prop
  have hangle (k : Fin N) : ∀ᶠ q : ℂ × (Fin N → ℝ) in 𝓝 (s, θ),
      q.2 k ∈ Icc (-rightBranchEndpoint S - β₀) β₀ := by
    have hk : θ k ∈ Ioo (-rightBranchEndpoint S - β₀) β₀ :=
      ⟨by linarith [(hθ k).1], (hθ k).2.trans_lt hb0⟩
    have hc : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 k) (s, θ) := by fun_prop
    exact (hc.eventually (isOpen_Ioo.mem_nhds hk)).mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hdiff : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 i - q.2 j) (s, θ) := by fun_prop
  have htangent : (fun q : ℂ × (Fin N → ℝ) =>
      ∑ k, actualCovarianceAngularVelocity η τ ξ k q) =ᶠ[𝓝 (s, θ)] (fun _ => 0) := by
    filter_upwards [hsim.eventually (Ioi_mem_nhds hs),
      hdist.eventually (Iio_mem_nhds (hsnear.trans hdr)),
      Filter.eventually_all.mpr hangle, hdiff.eventually_ne (sub_ne_zero.mpr hij)] with q hqs hqd hqθ hqij
    exact (hd N hN q.1 hqs hqd τ hτr ξ hξ q.2 hqθ i j (sub_ne_zero.mp hqij)).2.2.2.2
  have hFtangent : (fun q : ℂ × (Fin N → ℝ) => ∑ k,
      actualCovarianceAngularVelocity η τ ξ k q * actualCoordinateDeterminant η τ ξ q *
        (actualSignedProductKernel σ η τ ξ q * actualTransportDescendant η τ ξ b n q))
      =ᶠ[𝓝 (s, θ)] (fun _ => 0) := by
    filter_upwards [htangent] with q hq
    rw [← Finset.sum_mul, ← Finset.sum_mul, hq, zero_mul, zero_mul]
  have hdiv := tangent_current_constrained_divergence
    (fun k q => actualCovarianceAngularVelocity η τ ξ k q * actualCoordinateDeterminant η τ ξ q *
      (actualSignedProductKernel σ η τ ξ q * actualTransportDescendant η τ ξ b n q))
    actualAngularDirection (s, θ) anchor (fun k => ((hV k).mul hJ).mul (hK.mul hnd)) hFtangent
  rw [hdiv]
  exact exact_constructed_frozen_current (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ)
    (actualSignedProductKernel σ η τ ξ) (actualTransportDescendant η τ ξ b n)
    hχ₂ hBd hK hnd hdet hfreeze


theorem exists_actual_complete_density_current_buffer (S : ℝ)
    (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        ∀ i j, θ i ≠ θ j → ∀ anchor : Fin N,
        ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ∀ cutoff : (ℂ × (Fin N → ℝ)) → ℂ, ContDiffAt ℝ ∞ cutoff (s, θ) → ∀ n : ℕ,
        let b := actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ cutoff)
        ContDiffAt ℝ ∞ (b n) (s, θ) ∧
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y *
              (actualSignedProductKernel σ η τ ξ y * b n y)) actualTimeDirection (s, θ) -
            (∑ k ∈ Finset.univ.erase anchor,
              scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
                actualCoordinateDeterminant η τ ξ y * (actualSignedProductKernel σ η τ ξ y * b n y))
                (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) * actualSignedProductKernel σ η τ ξ (s, θ) *
            b (n + 1) (s, θ) := by
  obtain ⟨r₁, hr₁, hnum⟩ := exists_actual_initialAmplitude_smooth S hS
  obtain ⟨β₂, hβ₂, hβ₂1, hcurrent⟩ := exists_actual_iterated_constrained_current_buffer S hS
  let β := min r₁ β₂
  have hβ : 0 < β := lt_min hr₁ hβ₂
  have hb1 : β ≤ r₁ := min_le_left _ _
  have hb2 : β ≤ β₂ := min_le_right _ _
  have hb := (rightBranchEndpoint_lt_pi S hS.1).le
  refine ⟨β, hβ, hb2.trans hβ₂1, ?_⟩
  intro η hη
  obtain ⟨δ₂, hδ₂, _, hc⟩ := hcurrent η hη
  let δ := min β δ₂
  have hδ : 0 < δ := lt_min hβ hδ₂
  have hdβ : δ ≤ β := min_le_left _ _
  have hd1 : δ ≤ r₁ := hdβ.trans hb1
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor σ hσ cutoff hcut n
  have hθ1 : ∀ k, θ k ∈ Icc (-Real.pi - r₁) r₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β₂) β₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb2⟩
  have hn := hnum N hN s hs (hsnear.trans_le hd1) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hd1⟩ hξ θ hθ1 cutoff hcut
  exact hc N hN s hs (hsnear.trans_le hd2) τ ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ
    hθ2 i j hij anchor σ hσ (actualInitialAmplitude η τ ξ cutoff) hn n

end IsingBulk.AnisoF002.Isotropic
