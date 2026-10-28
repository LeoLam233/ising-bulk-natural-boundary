import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFramePullback
import IsingBulk.HT22.Tail.FrameCalculus
import IsingBulk.Preferred22.FrameWords

/-! All real smooth fixed-v frame words pull back actual complex partial
words. Canonical multilinear calculus is shared; the source frames are new. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem coordinateFrame_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Fin N)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    coordinateFrame τ p m a F s θ=coordinateFrame τ p m a G s θ := by
  have hh := (preferredFrame_derivatives_congr_open F G Ω hΩ he s θ hz).2
  unfold coordinateFrame
  simp_rw [hh]

theorem parameterFrame_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    parameterFrame τ p m F s θ=parameterFrame τ p m G s θ := by
  obtain ⟨hs,hθ⟩ := preferredFrame_derivatives_congr_open F G Ω hΩ he s θ hz
  unfold parameterFrame
  rw [hs]
  simp_rw [hθ]

/-- All actual frame words agree with canonical complex partial words on
every open physical chart. There is no assumed commutation identity. -/
theorem frameJet_pullback_open {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,sourceCoordinate τ p m z.1 z.2))
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs s θ=
      preferredComplexFrameJet F xs (s,sourceCoordinate τ p m s θ) := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    have he (z : ℂ × (Fin N → ℝ)) (hz : z∈Ω) :
        frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs z.1 z.2=
          preferredComplexFrameJet F xs (z.1,sourceCoordinate τ p m z.1 z.2) := ih z.1 z.2 hz
    have hpart := (preferredComplexFrameJet_analyticAt F xs _ (hF (s,θ) hz)).differentiableAt
    cases a with
    | none =>
      change parameterFrame τ p m
        (frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs) s θ=_
      rw [parameterFrame_congr_open τ p m _
        (fun t x => preferredComplexFrameJet F xs (t,sourceCoordinate τ p m t x)) Ω hΩ he s θ hz]
      exact parameterFrame_pullback τ δ p m hp hm s θ (hpoint (s,θ) hz)
        (preferredComplexFrameJet F xs) hpart
    | some a =>
      change coordinateFrame τ p m a
        (frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs) s θ=_
      rw [coordinateFrame_congr_open τ p m a _
        (fun t x => preferredComplexFrameJet F xs (t,sourceCoordinate τ p m t x)) Ω hΩ he s θ hz]
      exact coordinateFrame_pullback τ δ p m hp hm s θ (hpoint (s,θ) hz)
        (preferredComplexFrameJet F xs) hpart a


end
end IsingBulk.HT22.Tail
