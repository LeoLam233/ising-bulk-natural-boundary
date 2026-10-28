import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFrameBounds
import IsingBulk.Preferred22.FrameDomain

/-! Pointwise fixed-v pullback with the open physical chart proved internally. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem frameJet_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F (s,sourceCoordinate τ p m s θ))
    (xs : List (Option (Fin N))) :
    frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs s θ=
      preferredComplexFrameJet F xs (s,sourceCoordinate τ p m s θ) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (sourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,sourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have ha := hΨ.tendsto.eventually hF.eventually_analyticAt
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and ha)
  exact frameJet_pullback_open τ δ p m (hp.differentiable (by simp))
    (hm.differentiable (by simp)) Ω hΩ (fun z hz => (hΩsub hz).1)
    F (fun z hz => (hΩsub hz).2) xs s θ hz


/-- A component of a genuine analytic vector field has no extra N loss. -/
theorem residual_frameJet_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hF : AnalyticAt ℂ (fun x : SourcePoint N => sourceResidual x.1 x.2)
      (s,sourceCoordinate τ p m s θ))
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length (fun x : SourcePoint N => sourceResidual x.1 x.2)
      (s,sourceCoordinate τ p m s θ)‖≤C) (i : Fin N) :
    ‖frameJet τ p m (fun t x => sourceResidual t (sourceCoordinate τ p m t x) i) xs s θ‖≤C := by
  let F : SourcePoint N → (Fin N → ℂ) := fun x => sourceResidual x.1 x.2
  have hFi : AnalyticAt ℂ (fun x : SourcePoint N => F x i)
      (s,sourceCoordinate τ p m s θ) :=
    ((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp hF
  rw [frameJet_pullback τ δ p m hp hm s θ hpoint hθ (fun x => F x i) hFi xs,
    preferredComplexFrameJet_apply F xs _ hF i,
    preferredComplexFrameJet_eq_iteratedFDeriv F xs _ hF]
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)
        (preferredFrameDirections xs)‖ := norm_le_pi_norm _ i
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖ *
        ∏ k, ‖preferredFrameDirections xs k‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        preferredFrameDirections_norm_le xs k)) (by positivity) hC
    _ = _ := mul_one C

theorem frameJet_pullback_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (F : SourcePoint N → ℂ) (hF : AnalyticAt ℂ F (s,sourceCoordinate τ p m s θ))
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖≤C) :
    ‖frameJet τ p m (fun t x => F (t,sourceCoordinate τ p m t x)) xs s θ‖≤C := by
  rw [frameJet_pullback τ δ p m hp hm s θ hpoint hθ F hF xs,
    preferredComplexFrameJet_eq_iteratedFDeriv F xs _ hF]
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,sourceCoordinate τ p m s θ)‖ *
        ∏ k, ‖preferredFrameDirections xs k‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        preferredFrameDirections_norm_le xs k)) (by positivity) hC
    _ = _ := mul_one C

end
end IsingBulk.HT22.Tail
