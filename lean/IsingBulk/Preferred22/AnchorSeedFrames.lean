import IsingBulk.Preferred22.AnchorCoefficientBounds

/-! Actual source instantiation of the anchored scalar recurrence bounds.
Only finite norms of original source factors enter; the smoothness and
physical identification of every descendant are constructed locally. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem preferred_strict_frame_chart {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hpoint : PreferredFramePoint τ δ p m s θ) (hstrict : ∀ i,θ i∈Ioo (-Real.pi-δ) δ) :
    ∃ Ω : Set (ℂ × (Fin N → ℝ)),IsOpen Ω ∧ (s,θ)∈Ω ∧
      (∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) ∧
      ∀ z∈Ω,∀ i,z.2 i∈Ioo (-Real.pi-δ) δ := by
  have hreg : PreferredSourceRegime τ δ p m (s,θ) :=
    ⟨hpoint.trace_re,hpoint.trace_im,hpoint.trace_cap,hstrict,hpoint.upper⟩
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp
    ((preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hstrict).and
      ((preferredSourceRegime_isOpen τ δ p m hp.continuous hm.continuous).mem_nhds hreg))
  exact ⟨Ω,hΩ,hz,fun z hz => (hΩsub hz).1,fun z hz => (hΩsub hz).2.2.2.2.1⟩

/-- Every actual strict anchor point has the full physical factorization,
without a supplied neighborhood or any differentiated-series assumption. -/
theorem preferred_anchor_factorization_at {N : ℕ} (hN : 0<N)
    (a : Fin N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hstrict : ∀ i,θ i∈Ioo (-Real.pi-δ) δ) (j : ℕ) :
    preferredTransportedDensity (.anchor a) τ η p m r j s θ=
      preferredCoordinateJacobian τ p m s θ*preferredCellRegularScalar (.anchor a) τ η p m r j s θ := by
  obtain ⟨Ω,hΩ,hz,hΩpoint,hΩstrict⟩ := preferred_strict_frame_chart τ δ p m hp hm s θ hpoint hstrict
  exact preferred_anchor_factorization_on_chart hN a τ δ η p m r hη hp hm hr
    Ω hΩ hΩpoint hΩstrict j (s,θ) hz

/-- The finite seed norm is derived from its actual real cell weight and
full complex normalized amplitude, and propagated through the literal
anchor scalar recursion on a constructed genuine source chart. -/
theorem preferred_anchor_scalar_bound_at {N : ℕ}
    (a : Fin N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hstrict : ∀ i,θ i∈Ioo (-Real.pi-δ) δ)
    (hAa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (J : ℕ) (M W A : ℝ) (hM : 0≤M) (hW : 0≤W) (hA : 0≤A)
    (hB : ∀ i,∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualAnchor t (preferredSourceCoordinate τ p m t x) a i) ys s θ‖≤M)
    (hweight : ∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m (fun _ x => (preferredCellWeight (.anchor a) η p m r x:ℂ)) ys s θ‖≤W)
    (hamp : ∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m (fun t x => preferredRegularAmplitude t (preferredSourceCoordinate τ p m t x)) ys s θ‖≤A) :
    ∀ j≤J,‖preferredCellRegularScalar (.anchor a) τ η p m r j s θ‖≤
      (1+2^(J+1)*(N:ℝ)*M)^j*(2^J*W*A) := by
  obtain ⟨Ω₀,hΩ₀,hz₀,hΩ₀point,_hΩ₀strict⟩ := preferred_strict_frame_chart τ δ p m hp hm s θ hpoint hstrict
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hAEv : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ),
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredRegularAmplitude x.1 x.2)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2) :=
    (continuousAt_fst.prodMk hχ).tendsto.eventually hAa.eventually_analyticAt
  have hΩEv : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), z∈Ω₀ := hΩ₀.mem_nhds hz₀
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hΩEv.and hAEv)
  have hΩpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => hΩ₀point z (hΩsub hz).1
  have hAm : PreferredMixedSmoothOn (fun z => preferredRegularAmplitude z.1
      (preferredSourceCoordinate τ p m z.1 z.2)) Ω :=
    preferred_analytic_pullback_mixed τ δ p m hp hm Ω hΩpoint _ (fun _ hz => (hΩsub hz).2)
  have hBm (i : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredResidualField (.anchor a) z.1 (preferredSourceCoordinate τ p m z.1 z.2) i) Ω := by
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hΩpoint
      (fun z : ℂ × (Fin N → ℂ) => preferredResidualAnchor z.1 z.2 a i)
    intro z hz
    exact analyticAt_pi_iff.mp (preferredResidualAnchor_analyticAt a _ _ (hΩpoint z hz).inverse_analytic
      ((hΩpoint z hz).inverse_q_ne_zero a)) i
  let weight := fun x : Fin N → ℝ => (preferredCellWeight (.anchor a) η p m r x:ℂ)
  have hwreal : ContDiff ℝ ∞ (preferredCellWeight (.anchor a) η p m r : (Fin N → ℝ) → ℝ) := by
    unfold preferredCellWeight preferredLowerWeight lowerWeight preferredAnchorWeight occupancy
    fun_prop
  have hwc : ContDiff ℝ ∞ weight := Complex.ofRealCLM.contDiff.comp hwreal
  have hwm : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => weight z.2) Ω :=
    fun z _ => ⟨hwc.contDiffAt.comp z contDiffAt_snd,differentiableAt_const (𝕜:=ℂ) (x:=z.1) (weight z.2)⟩
  have hseedm : PreferredMixedSmoothOn
      (fun z => preferredCellRegularSeed (.anchor a) τ η p m r z.1 z.2) Ω := hwm.mul hAm
  have hseed (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ p m (preferredCellRegularSeed (.anchor a) τ η p m r) ys s θ‖≤2^J*W*A :=
    preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint (fun _ x => weight x)
      (fun t x => preferredRegularAmplitude t (preferredSourceCoordinate τ p m t x))
      hwm hAm s θ hz J W A hW hA hweight hamp ys hys
  intro j hj
  have hh := preferredCellRegularScalar_frame_bound (.anchor a) τ δ η p m r hp hm Ω hΩ hΩpoint
    hBm hseedm s θ hz J M (2^J*W*A) hM (by positivity) hB hseed j hj [] (by simpa using hj)
  exact hh

end
end IsingBulk.Preferred22
