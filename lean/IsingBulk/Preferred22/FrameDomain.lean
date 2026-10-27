import IsingBulk.Preferred22.FrameWords
import IsingBulk.Preferred22.PhysicalTransport

/-! Genuine open physical source charts for the all-order frame pullback.
The chart is constructed from strict physical branch margins and smooth real
occupancy data, rather than assumed as a calculus interface. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredFramePoint_eventually {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ) :
    ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), PreferredFramePoint τ δ p m z.1 z.2 := by
  have hs : s≠0 := by
    intro hz
    have hh := hpoint.trace_im
    rw [hz] at hh
    simp [temperatureTrace] at hh
  have ht : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => temperatureTrace z.1) (s,θ) := by
    unfold temperatureTrace
    exact continuousAt_fst.add (continuousAt_fst.inv₀ hs)
  have htr : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => (temperatureTrace z.1).re) (s,θ) :=
    Complex.continuous_re.continuousAt.comp ht
  have hti : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => (temperatureTrace z.1).im) (s,θ) :=
    Complex.continuous_im.continuousAt.comp ht
  have hre := (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (0:ℝ)) (s,θ)).eventually_lt htr hpoint.trace_re
  have him := (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (0:ℝ)) (s,θ)).eventually_lt hti hpoint.trace_im
  have hcap := htr.eventually_lt continuousAt_const hpoint.trace_cap
  have hangle : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), ∀ i, z.2 i∈Ioo (-Real.pi-δ) δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hi : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => z.2 i) (s,θ) := by fun_prop
    exact ((continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => -Real.pi-δ) (s,θ)).eventually_lt hi (hθ i).1).and
      (hi.eventually_lt continuousAt_const (hθ i).2)
  have hw : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ),
      ∀ i, 0<(temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im := by
    apply Filter.eventually_all.mpr
    intro i
    have hpc := hp.continuous
    have hmc := hm.continuous
    have hangle : Continuous (fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2 i) := by
      unfold deformedAngles balancedShift occupancy
      fun_prop
    have hh : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
        (temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im) (s,θ) :=
      Complex.continuous_im.continuousAt.comp
        (ht.sub (Complex.continuous_cos.continuousAt.comp hangle.continuousAt))
    exact (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (0:ℝ)) (s,θ)).eventually_lt hh (hpoint.upper i)
  have hmat : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m z.2).det) (s,θ) := by
    have hmcont : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredContourMatrix τ p m z.2) :=
      (preferredContourMatrix_contDiff τ p m hp hm).comp contDiff_snd
    have hentry (i j : Fin N) := (contDiff_pi.mp (contDiff_pi.mp hmcont i) j).continuous.continuousAt (x := (s,θ))
    simp only [Matrix.det_apply]
    fun_prop
  have hmat' := hmat.eventually_ne hpoint.matrix
  filter_upwards [hre,him,hcap,hangle,hw,hmat'] with z hzr hzi hzc hzθ hzW hzM
  exact ⟨hpoint.delta_pos,hpoint.delta_lt,hzr,hzi,hzc,
    fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩,hzW,hzM⟩

/-- All source-frame words equal the literal complex partial words near
every actual interior physical point. No open-chart hypothesis survives. -/
theorem preferredFrameJet_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F (s,preferredSourceCoordinate τ p m s θ))
    (xs : List (Option (Fin N))) :
    preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)) xs s θ=
      preferredComplexFrameJet F xs (s,preferredSourceCoordinate τ p m s θ) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have ha := hΨ.tendsto.eventually hF.eventually_analyticAt
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and ha)
  exact preferredFrameJet_pullback_open τ δ p m (hp.differentiable (by simp))
    (hm.differentiable (by simp)) Ω hΩ (fun z hz => (hΩsub hz).1)
    F (fun z hz => (hΩsub hz).2) xs s θ hz

end
end IsingBulk.Preferred22
