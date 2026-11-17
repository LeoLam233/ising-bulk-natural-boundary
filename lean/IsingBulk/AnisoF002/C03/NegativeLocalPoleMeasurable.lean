import IsingBulk.AnisoF002.C03.NegativeMeasurablePole

/-!
# A measurable representative of the exact local pole remainder

Only values outside the proved analytic disk are set to zero.  On that
disk the representative equals the original double divided difference,
including both removable diagonal values.  This is a measure-theoretic
extension of the actual function, not a replacement physical integrand.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

variable {X : Type*}

def diskKernelExtension (R : ℝ) (F : ℂ → X → ℂ) (t : ℂ) (x : X) : ℂ :=
  if t ∈ Metric.ball 0 R then F t x else 0

theorem diskKernelExtension_measurable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {R : ℝ} {F : ℂ → X → ℂ}
    (hc : ContinuousOn (Function.uncurry F) {p : ℂ × X | p.1 ∈ Metric.ball 0 R}) :
    Measurable (Function.uncurry (diskKernelExtension R F)) := by
  classical
  convert hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)))
      (Metric.isOpen_ball.preimage continuous_fst).measurableSet using 1
  rfl

theorem diskKernelExtension_eq {R : ℝ} (F : ℂ → X → ℂ) {t : ℂ}
    (ht : t ∈ Metric.ball 0 R) (x : X) : diskKernelExtension R F t x = F t x := by
  simp only [diskKernelExtension, ht, ↓reduceIte]

theorem diskKernelExtension_eventuallyEq {R : ℝ} (F : ℂ → X → ℂ) {t : ℂ}
    (ht : t ∈ Metric.ball 0 R) (x : X) :
    (fun u => diskKernelExtension R F u x) =ᶠ[𝓝 t] (fun u => F u x) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
  exact diskKernelExtension_eq F hu x

theorem filledPoleNumerator_eq_of_local_eq {H H' F F' : ℂ → ℂ} {P t : ℂ}
    (hH : H t = H' t) (hF : F t = F' t) (hnear : F =ᶠ[𝓝 P] F') (n : ℕ) :
    filledPoleNumerator H F n P t = filledPoleNumerator H' F' n P t := by
  unfold filledPoleNumerator
  rw [hH, hF, dslope_eq_of_local_eq hnear hF]

theorem exists_measurable_exact_pole_remainder
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {R : ℝ} {H F : ℂ → X → ℂ}
    {P : X → ℂ} (n : ℕ)
    (hH : ContinuousOn (Function.uncurry H) {p : ℂ × X | p.1 ∈ Metric.ball 0 R})
    (hF : ContinuousOn (Function.uncurry F) {p : ℂ × X | p.1 ∈ Metric.ball 0 R})
    (hP : Measurable P) (hPin : ∀ x, P x ∈ Metric.ball 0 R)
    (hFd : ∀ x, DifferentiableAt ℂ (fun t => F t x) (P x))
    (hKd : ∀ x, DifferentiableAt ℂ
      (filledPoleNumerator (fun t => H t x) (fun t => F t x) n (P x)) (P x)) :
    ∃ G : ℂ → X → ℂ, Measurable (Function.uncurry G) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) R, ∀ x,
        G t x = dslope (filledPoleNumerator (fun u => H u x) (fun u => F u x) n (P x)) (P x) t := by
  let H' := diskKernelExtension R H
  let F' := diskKernelExtension R F
  let K : ℂ → X → ℂ := fun t x =>
    filledPoleNumerator (fun u => H u x) (fun u => F u x) n (P x) t
  let K' : ℂ → X → ℂ := fun t x =>
    filledPoleNumerator (fun u => H' u x) (fun u => F' u x) n (P x) t
  have hFnear (x : X) : (fun t => F' t x) =ᶠ[𝓝 (P x)] (fun t => F t x) :=
    diskKernelExtension_eventuallyEq F (hPin x) x
  have hKval (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) R) (x : X) : K' t x = K t x :=
    filledPoleNumerator_eq_of_local_eq (diskKernelExtension_eq H ht x)
      (diskKernelExtension_eq F ht x) (hFnear x) n
  have hKnear (x : X) : (fun t => K' t x) =ᶠ[𝓝 (P x)] (fun t => K t x) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (hPin x)] with t ht
    exact hKval t ht x
  have hmK : Measurable (Function.uncurry K') :=
    measurable_filledPoleNumerator (diskKernelExtension_measurable hH)
      (diskKernelExtension_measurable hF) hP
      (fun x => (hFd x).congr_of_eventuallyEq (hFnear x)) n
  refine ⟨fun t x => dslope (fun u => K' u x) (P x) t,
    measurable_dslope_moving_center hmK hP
      (fun x => (hKd x).congr_of_eventuallyEq (hKnear x)), ?_⟩
  intro t ht x
  exact dslope_eq_of_local_eq (hKnear x) (hKval t ht x)

end
end IsingBulk.AnisoF002.NegativeHT
