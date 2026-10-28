import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFrameWords
import IsingBulk.HT22.Transport.FieldNeighborhood.JetTheorem
import IsingBulk.Preferred22.RegularFrameJets

/-! Joint Cauchy bounds control genuine fixed-v source-frame words.
Every parameter or coordinate letter contributes to the total jet order. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem frameJet_pullback_bound_open {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,sourceCoordinate τ p m z.1 z.2))
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖≤C) :
    ‖frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs s θ‖≤C := by
  rw [frameJet_pullback_open τ δ p m hp hm Ω hΩ hpoint F hF xs s θ hz,
    preferredComplexFrameJet_eq_iteratedFDeriv F xs _ (hF (s,θ) hz)]
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖ *
        ∏ k, ‖preferredFrameDirections xs k‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        preferredFrameDirections_norm_le xs k)) (by positivity) hC
    _ = _ := mul_one C

/-- Vector-valued field estimates imply bounds for every actual angular
component without an extra factor depending on particle number. -/
theorem residual_frameJet_bound_open {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hF : ∀ z∈Ω, AnalyticAt ℂ (fun x : SourcePoint N => sourceResidual x.1 x.2)
      (z.1,sourceCoordinate τ p m z.1 z.2))
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length (fun x : SourcePoint N => sourceResidual x.1 x.2)
      (s,sourceCoordinate τ p m s θ)‖≤C) (i : Fin N) :
    ‖frameJet τ p m (fun t x => sourceResidual t (sourceCoordinate τ p m t x) i) xs s θ‖≤C := by
  let F : SourcePoint N → (Fin N → ℂ) := fun x => sourceResidual x.1 x.2
  have hFi : ∀ z∈Ω, AnalyticAt ℂ (fun x : SourcePoint N => F x i)
      (z.1,sourceCoordinate τ p m z.1 z.2) := by
    intro z hz
    exact ((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (hF z hz)
  rw [frameJet_pullback_open τ δ p m hp hm Ω hΩ hpoint (fun x => F x i) hFi xs s θ hz,
    preferredComplexFrameJet_apply F xs _ (hF (s,θ) hz) i,
    preferredComplexFrameJet_eq_iteratedFDeriv F xs _ (hF (s,θ) hz)]
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)
        (preferredFrameDirections xs)‖ := norm_le_pi_norm _ i
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖ *
        ∏ k, ‖preferredFrameDirections xs k‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        preferredFrameDirections_norm_le xs k)) (by positivity) hC
    _ = _ := mul_one C

end
end IsingBulk.HT22.Tail
