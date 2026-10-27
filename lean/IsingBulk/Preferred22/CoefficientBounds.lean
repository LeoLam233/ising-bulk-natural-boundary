import IsingBulk.Preferred22.CoefficientCalculus
import IsingBulk.Preferred22.CoefficientNorm

/-! The literal normalized scalar coefficient satisfies the exact marked
loss budget from bounds only on the original seed/B/kernel frame jets.
Neither generated coefficients nor any tail estimate is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredWordCoefficient_bound_of_source_frames {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hBa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (R D : ℝ) (hR : 1≤R) (hdiam : 0<preferredAngularDiameter θ)
    (hdiamD : preferredAngularDiameter θ≤D) (hD : 1≤D)
    (L M j : ℕ)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
        preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) xs s θ‖≤R)
    (w : PreferredMarkedWord N j) :
    ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredWordCoefficient τ η p m r j w s θ‖≤
      ((preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j))^N *
        (N:ℝ)^(L+M*(2*j+1)+j)/preferredAngularDiameter θ^(preferredWordLoss j w) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have ha := hΨ.tendsto.eventually hBa.eventually_analyticAt
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and ha)
  have hA := preferredAtomValue_mixed τ δ η p m r hη hp hm hr Ω hΩ
    (fun z hz => (hΩsub hz).1) (fun z hz => (hΩsub hz).2)
  rw [preferredWordCoefficient_eq_terms τ η p m r Ω hΩ hA j w s θ hz]
  exact preferredCoefficientTerms_sum_bound hN τ η p m r s θ
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) R (preferredAngularDiameter θ) D hR hdiam hdiamD hD
    L M j w hseed hB hK

end
end IsingBulk.Preferred22
