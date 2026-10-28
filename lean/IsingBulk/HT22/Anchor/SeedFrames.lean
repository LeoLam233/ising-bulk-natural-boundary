import IsingBulk.HT22.Anchor.CoefficientBounds
import IsingBulk.Preferred22.AnchorSeedFrames
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Actual weighted odd seed and corrected field bounds imply bounds on
the genuine generated scalars by finite Leibniz induction. -/
theorem scalar_bound_at {N : ℕ}
    (hN : 0<N) (a : Fin N) (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hstrict : ∀ i,θ i∈Ioo (-Real.pi-δ) δ)
    (hAa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (J : ℕ) (M W A : ℝ) (hM : 0≤M) (hW : 0≤W) (hA : 0≤A)
    (hB : ∀ i,∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m
        (fun t x => movingSourceResidual a τ p m t x i) ys s θ‖≤M)
    (hweight : ∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m (fun _ x => (preferredCellWeight (.anchor a) η p m r x:ℂ)) ys s θ‖≤W)
    (hamp : ∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m (fun t x => amplitude σ t (preferredSourceCoordinate τ p m t x)) ys s θ‖≤A) :
    ∀ j≤J,‖regularTransportedScalar a σ τ η p m r j s θ‖≤
      (1+2^(J+1)*(N:ℝ)*M)^j*(2^J*W*A) := by
  obtain ⟨Ω₀,hΩ₀,hz₀,hΩ₀point,_hΩ₀strict⟩ := preferred_strict_frame_chart τ δ p m hp hm s θ hpoint hstrict
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hAEv : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ),
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => amplitude σ x.1 x.2)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2) :=
    (continuousAt_fst.prodMk hχ).tendsto.eventually hAa.eventually_analyticAt
  have hΩEv : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), z∈Ω₀ := hΩ₀.mem_nhds hz₀
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hΩEv.and hAEv)
  have hΩpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => hΩ₀point z (hΩsub hz).1
  have hAm : PreferredMixedSmoothOn (fun z => amplitude σ z.1
      (preferredSourceCoordinate τ p m z.1 z.2)) Ω :=
    preferred_analytic_pullback_mixed τ δ p m hp hm Ω hΩpoint _ (fun _ hz => (hΩsub hz).2)
  let weight := fun x : Fin N → ℝ => (preferredCellWeight (.anchor a) η p m r x:ℂ)
  have hwreal : ContDiff ℝ ∞ (preferredCellWeight (.anchor a) η p m r : (Fin N → ℝ) → ℝ) := by
    unfold preferredCellWeight preferredLowerWeight lowerWeight preferredAnchorWeight occupancy
    fun_prop
  have hwc : ContDiff ℝ ∞ weight := Complex.ofRealCLM.contDiff.comp hwreal
  have hwm : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => weight z.2) Ω :=
    fun z _ => ⟨hwc.contDiffAt.comp z contDiffAt_snd,differentiableAt_const (𝕜:=ℂ) (x:=z.1) (weight z.2)⟩
  have hseed (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ p m (regularSeed a σ τ η p m r) ys s θ‖≤2^J*W*A := by
    have he : regularSeed a σ τ η p m r = fun t x => weight x*amplitude σ t (preferredSourceCoordinate τ p m t x) := by
      funext t x
      exact congrArg (fun z : ℂ => weight x*z) (fixedAmplitude_source_adapter σ τ p m t x)
    rw [he]
    exact
      preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint (fun _ x => weight x)
      (fun t x => amplitude σ t (preferredSourceCoordinate τ p m t x))
      hwm hAm s θ hz J W A hW hA hweight hamp ys hys
  intro j hj
  have hh := regularScalar_frame_bound hN a σ hσ τ δ η p m r hη hp hm hr Ω hΩ hΩpoint s θ hz J M (2^J*W*A) hM (by positivity) hB hseed j hj [] (by simpa using hj)
  exact hh

end
end IsingBulk.HT22.Anchor
