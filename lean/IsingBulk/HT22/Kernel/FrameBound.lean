import IsingBulk.HT22.Kernel.CompactJets
import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFrameDomain

namespace IsingBulk.HT22.Kernel
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Filter Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem fixed_frame_analytic_projection_bound {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (F G : E → ℂ) (L : (ℂ × (Fin N → ℂ)) →L[ℂ] E)
    (hL : ∀ z, ‖L z‖≤‖z‖)
    (hG : AnalyticAt ℂ G (L (s,sourceCoordinate τ p m s θ)))
    (heq : F =ᶠ[𝓝 (L (s,sourceCoordinate τ p m s θ))] G)
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length G (L (s,sourceCoordinate τ p m s θ))‖≤C) :
    ‖frameJet τ p m (fun t x => F (L (t,sourceCoordinate τ p m t x))) xs s θ‖≤C := by
  let z := (s,sourceCoordinate τ p m s θ)
  have hF : AnalyticAt ℂ F (L z) := hG.congr heq.symm
  have hFL : AnalyticAt ℂ (F ∘ L) z := hF.comp (L.analyticAt z)
  change ‖frameJet τ p m
    (fun t x => (F ∘ L) (t,sourceCoordinate τ p m t x)) xs s θ‖≤C
  rw [frameJet_pullback τ δ p m hp hm s θ hpoint hθ (F ∘ L) hFL xs,
    preferredComplexFrameJet_eq_iteratedFDeriv (F ∘ L) xs z hFL]
  have he := heq.comp_tendsto (L.continuous.tendsto z)
  rw [(he.iteratedFDeriv ℂ xs.length).eq_of_nhds,
    analytic_iteratedFDeriv_comp_linear L G z hG xs.length]
  change ‖iteratedFDeriv ℂ xs.length G (L z)
    (fun k => L (preferredFrameDirections xs k))‖≤C
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length G (L z)‖ *
        ∏ k, ‖L (preferredFrameDirections xs k)‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        (hL _).trans (preferredFrameDirections_norm_le xs k))) (by positivity) hC
    _ = _ := mul_one C

end
end IsingBulk.HT22.Kernel
