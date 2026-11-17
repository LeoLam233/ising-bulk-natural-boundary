import IsingBulk.AnisoF002.C03.IsotropicKernelCurrent

/-!
# Exact constrained transport of the full signed physical kernel

The scalar current acts on the complete physical kernel times an
arbitrary differentiable amplitude. The kernel is unchanged, and the
amplitude is transformed by the actual regular transport operator.
All geometry, current, phase, and tangency hypotheses are discharged
on a single actual neighborhood selected before N.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def actualTransportAmplitude {N : ℕ} (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) : (ℂ × (Fin N → ℝ)) → ℂ :=
  regularTransportAmplitude (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (actualCovarianceRegularField η τ ξ) b

/-- The complete signed physical product kernel is frozen by the
actual constrained current. The statement includes every proper
partial diagonal and every actual occupancy fraction. -/
theorem exists_actual_constrained_frozen_kernel_current (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j → ∀ anchor : Fin N,
        ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ∀ b : (ℂ × (Fin N → ℝ)) → ℂ, DifferentiableAt ℝ b (s, θ) →
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y *
              (actualSignedProductKernel σ η τ ξ y * b y)) actualTimeDirection (s, θ) -
            (∑ k ∈ Finset.univ.erase anchor,
              scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
                actualCoordinateDeterminant η τ ξ y * (actualSignedProductKernel σ η τ ξ y * b y))
                (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) * actualSignedProductKernel σ η τ ξ (s, θ) *
            actualTransportAmplitude η τ ξ b (s, θ) := by
  obtain ⟨r₁, hr₁, hdata⟩ := exists_actual_right_current_data S η hS hη
  obtain ⟨r₂, hr₂, hconstrained⟩ := exists_actual_right_constrained_current S η hS hη
  let δ := min r₁ r₂
  have hδ : 0 < δ := lt_min hr₁ hr₂
  have hd1 : δ ≤ r₁ := min_le_left _ _
  have hd2 : δ ≤ r₂ := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor σ hσ b hb
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₁) r₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₂) r₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd2⟩
  obtain ⟨hχ, hdet, hB, _, htangent⟩ := hdata N hN s hs (hsnear.trans_le hd1) τ
    ⟨hτ.1, hτ.2.trans hd1⟩ ξ hξ θ hθ1 i j hij
  obtain ⟨hK, hfreeze⟩ := actualSignedProductKernel_transport σ hσ η τ ξ hη hτ.1 hξ.1
    (s, θ) hs hχ hdet htangent
  let K : (ℂ × (Fin N → ℝ)) → ℂ := actualSignedProductKernel σ η τ ξ
  have hc := hconstrained N hN s hs (hsnear.trans_le hd2) τ
    ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ hθ2 i j hij anchor (fun y => K y * b y) (hK.mul hb)
  have hk := exact_constructed_regular_current (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ)
    (fun y => K y * b y) hχ hB (hK.mul hb) hdet
  have hf := exact_constructed_frozen_current (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ)
    K b hχ hB hK hb hdet hfreeze
  exact hc.trans (hk.symm.trans hf)

end IsingBulk.AnisoF002.Isotropic
