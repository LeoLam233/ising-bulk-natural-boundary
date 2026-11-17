import IsingBulk.AnisoF002.C03.IsotropicSmoothTransport

/-!
# Iteration of the actual constrained physical current

One radius, chosen before the particle number and transport order,
supports the entire smooth recurrence on every nonconstant actual right
configuration. Each identity retains the complete physical kernel and
all derivatives of the previously transported amplitude.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Set Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actualCovarianceRegularField_contDiffAt (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ i) q)
    (hB : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => rightCovarianceField p.1 p.2)
      (q.1, fun i => actualPhysicalCoordinate η τ ξ i q)) (i : ι) :
    ContDiffAt ℝ ∞ (actualCovarianceRegularField η τ ξ i) q := by
  have hχ' : ContDiffAt ℝ ∞
      (fun y => (y.1, fun j => actualPhysicalCoordinate η τ ξ j y)) q :=
    contDiffAt_fst.prodMk (contDiffAt_pi.mpr hχ)
  exact contDiffAt_pi.mp (hB.restrictScalars.contDiffAt.comp q hχ') i

/-- Smoothness is established for the actual covariance field, with
no supplied denominator, smooth-field, or inverse-Jacobian premise. -/
theorem exists_actual_right_smooth_data (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j →
        (∀ k, ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ k) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∀ k, ContDiffAt ℝ ∞ (actualCovarianceRegularField η τ ξ k) (s, θ)) := by
  obtain ⟨r₁, hr₁, hdata⟩ := exists_actual_right_current_data S η hS hη
  obtain ⟨r₂, hr₂, hcov⟩ := exists_actual_right_covariance_transport S η hS hη
  let δ := min r₁ r₂
  have hδ : 0 < δ := lt_min hr₁ hr₂
  have hd1 : δ ≤ r₁ := min_le_left _ _
  have hd2 : δ ≤ r₂ := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₁) r₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₂) r₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd2⟩
  obtain ⟨_, hdet, _⟩ := hdata N hN s hs (hsnear.trans_le hd1) τ
    ⟨hτ.1, hτ.2.trans hd1⟩ ξ hξ θ hθ1 i j hij
  obtain ⟨hB, _⟩ := hcov N hN s hs (hsnear.trans_le hd2) τ
    ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ hθ2 i j hij
  have hχ (k : Fin N) : ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ k) (s, θ) :=
    actualPhysicalCoordinate_contDiffAt η τ ξ k (s, θ) ⊤
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ k)
  exact ⟨hχ, hdet, actualCovarianceRegularField_contDiffAt η τ ξ (s, θ) hχ hB⟩

def actualTransportDescendant {N : ℕ} (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) (n : ℕ) : (ℂ × (Fin N → ℝ)) → ℂ :=
  regularTransportDescendant (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualCovarianceRegularField η τ ξ) b n

@[simp] theorem actualTransportDescendant_zero {N : ℕ} (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) : actualTransportDescendant η τ ξ b 0 = b := rfl

@[simp] theorem actualTransportDescendant_succ {N : ℕ} (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) (n : ℕ) :
    actualTransportDescendant η τ ξ b (n + 1) =
      actualTransportAmplitude η τ ξ (actualTransportDescendant η τ ξ b n) := rfl

/-- Every order of the actual constrained recurrence, on the same
neighborhood, with the actual complete physical kernel unchanged. -/
theorem exists_actual_iterated_constrained_current (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
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
  obtain ⟨r₁, hr₁, hdata⟩ := exists_actual_right_smooth_data S η hS hη
  obtain ⟨r₂, hr₂, hcurrent⟩ := exists_actual_constrained_frozen_kernel_current S η hS hη
  let δ := min r₁ r₂
  have hδ : 0 < δ := lt_min hr₁ hr₂
  have hd1 : δ ≤ r₁ := min_le_left _ _
  have hd2 : δ ≤ r₂ := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor σ hσ b hb n
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₁) r₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₂) r₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd2⟩
  obtain ⟨hχ, hdet, hB⟩ := hdata N hN s hs (hsnear.trans_le hd1) τ
    ⟨hτ.1, hτ.2.trans hd1⟩ ξ hξ θ hθ1 i j hij
  have hn := regularTransportDescendant_contDiffAt (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ)
    b hχ hB hb hdet n
  refine ⟨hn, ?_⟩
  exact hcurrent N hN s hs (hsnear.trans_le hd2) τ ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ
    hθ2 i j hij anchor σ hσ (actualTransportDescendant η τ ξ b n) (hn.differentiableAt (by simp))

end IsingBulk.AnisoF002.Isotropic
