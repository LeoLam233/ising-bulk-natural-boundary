import IsingBulk.HT22.Tail.SeedNormalization
import IsingBulk.Preferred22.SourceMixedFactors

/-! # Exact shared one-body seed calculus

The one-body scalar and original real weight are identical after the
explicit coordinate translation. This does not identify the odd determinant
or the mixed residual field with either LT construction.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem regularPhase_moving_adapter (t v : ℂ) :
    regularPhase t v=preferredRegularPhase t (v-preferredMovingBranch t) := by
  unfold regularPhase preferredRegularPhase
  rw [regularInverse_moving_adapter]
  ring

theorem regularOneBody_moving_adapter (t v : ℂ) :
    regularOneBody t v=preferredRegularOneBody t (v-preferredMovingBranch t) := by
  rw [regularOneBody,inverseV_moving_adapter,regularPhase_moving_adapter]
  rfl

/-- Exact equality of the seed coefficient, excluding every determinant.
Unlike the fixed-v residual or parameter frame this scalar is shared. -/
theorem regularSeedCoefficient_eq_shared {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) :
    regularSeedCoefficient τ η p m r t θ=preferredRegularSeedCoefficient τ η p m r t θ := by
  unfold regularSeedCoefficient preferredRegularSeedCoefficient
  simp_rw [regularOneBody_moving_adapter,sourceCoordinate_moving_adapter]

theorem regularSeedCoefficient_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z => regularSeedCoefficient τ η p m r z.1 z.2) Ω := by
  simp_rw [regularSeedCoefficient_eq_shared]
  exact preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint

/-- Local mixed regularity of the actual seed follows on the open physical
chart, with no hypothetical derivative bounds or descendant premises. -/
theorem regularSeedCoefficient_local_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (t : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m t θ)
    (hθ : ∀ i, θ i∈Set.Ioo (-Real.pi-δ) δ) :
    ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧ (t,θ)∈Ω ∧
      PreferredMixedSmoothOn (fun z => regularSeedCoefficient τ η p m r z.1 z.2) Ω := by
  have he := preferredFramePoint_eventually τ δ p m hp hm t θ hpoint hθ
  obtain ⟨Ω,hsub,hΩ,hz⟩ := mem_nhds_iff.mp he
  exact ⟨Ω,hΩ,hz,regularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω
    (fun z hz => hsub hz)⟩

end
end IsingBulk.HT22.Tail
