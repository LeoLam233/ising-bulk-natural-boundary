import IsingBulk.First.PeriodicWrapInvariant
import IsingBulk.First.ComplementVectors

/-! Paired angular periodicization for actual compact lifted double-chart bumps. -/
namespace IsingBulk.First
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

def doubleCenteredWrap {N : ℕ} (c u : DoubleAngularVector N) : DoubleAngularVector N :=
  (centeredWrap c.1 u.1,centeredWrap c.2 u.2)

def doublePeriodicizeBump {N : ℕ} (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ) (u : DoubleAngularVector N) : ℝ := w (doubleCenteredWrap c u)

def DoubleCoordinatePeriodic {N : ℕ} {A : Type*} (F : DoubleAngularVector N → A) : Prop :=
  ∀ u i, F (Function.update u.1 i (u.1 i+2*Real.pi),u.2) = F u ∧
    F (u.1,Function.update u.2 i (u.2 i+2*Real.pi)) = F u

theorem doublePeriodicizeBump_periodic {N : ℕ} (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ) : DoubleCoordinatePeriodic (doublePeriodicizeBump c w) := by
  intro u i
  simp only [doublePeriodicizeBump,doubleCenteredWrap,centeredWrap_update_period,and_self]

theorem doubleCoordinatePeriodic_wrap {N : ℕ} {A : Type*} (F : DoubleAngularVector N → A)
    (hF : DoubleCoordinatePeriodic F) (c u : DoubleAngularVector N) : F (doubleCenteredWrap c u) = F u := by
  unfold doubleCenteredWrap
  rw [coordinatePeriodic_centeredWrap (fun x => F (x,centeredWrap c.2 u.2))
      (fun x i => (hF (x,centeredWrap c.2 u.2) i).1)]
  exact coordinatePeriodic_centeredWrap (fun y => F (u.1,y)) (fun y i => (hF (u.1,y) i).2) c.2 u.2

theorem doubleCenteredWrap_pi_mem_box {N : ℕ} (u : DoubleAngularVector N) :
    doubleCenteredWrap ((fun _ => Real.pi),(fun _ => Real.pi)) u ∈ angleBox N ×ˢ angleBox N :=
  ⟨centeredWrap_pi_mem_angleBox u.1,centeredWrap_pi_mem_angleBox u.2⟩

theorem doublePeriodicizeBump_support_cos {N : ℕ} (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2)
    {u : DoubleAngularVector N} (hu : doublePeriodicizeBump c w u ≠ 0) (i : Fin N) :
    3/4 ≤ Real.cos (u.1 i-c.1 i) ∧ 3/4 ≤ Real.cos (u.2 i-c.2 i) := by
  have h := hsmall (doubleCenteredWrap c u) hu i
  simp only [doubleCenteredWrap,centeredWrap,add_sub_cancel_left] at h
  have h1 := Real.one_sub_sq_div_two_le_cos (x := periodicAngle (u.1 i-c.1 i))
  have h2 := Real.one_sub_sq_div_two_le_cos (x := periodicAngle (u.2 i-c.2 i))
  rw [periodicAngle_cos] at h1 h2
  have ha := abs_le.mp h.1
  have hb := abs_le.mp h.2
  constructor <;> nlinarith

theorem doublePeriodicizeBump_contDiff {N : ℕ} (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    ContDiff ℝ ∞ (doublePeriodicizeBump c w) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hX : ∀ i, 0 < Real.cos (u.1 i-c.1 i)
  · by_cases hY : ∀ i, 0 < Real.cos (u.2 i-c.2 i)
    · have hx : ContDiffAt ℝ ∞ (fun q : DoubleAngularVector N => centeredWrap c.1 q.1) u := by
        apply contDiffAt_pi.mpr
        intro i
        exact contDiffAt_const.add (ContDiffAt.comp (f := fun q : DoubleAngularVector N => q.1 i-c.1 i) (g := periodicAngle) u (periodicAngle_contDiffAt (hX i)) (by fun_prop))
      have hy : ContDiffAt ℝ ∞ (fun q : DoubleAngularVector N => centeredWrap c.2 q.2) u := by
        apply contDiffAt_pi.mpr
        intro i
        exact contDiffAt_const.add (ContDiffAt.comp (f := fun q : DoubleAngularVector N => q.2 i-c.2 i) (g := periodicAngle) u (periodicAngle_contDiffAt (hY i)) (by fun_prop))
      exact hw.contDiffAt.comp u (hx.prodMk hy)
    · push Not at hY
      obtain ⟨i,hi⟩ := hY
      have hc : ContinuousAt (fun q : DoubleAngularVector N => Real.cos (q.2 i-c.2 i)) u := by fun_prop
      have hn := hc.eventually (Iio_mem_nhds (show Real.cos (u.2 i-c.2 i) < 1/2 by linarith))
      have hz : doublePeriodicizeBump c w =ᶠ[𝓝 u] (fun _ => 0) := by
        filter_upwards [hn] with q hq
        by_contra he
        linarith [(doublePeriodicizeBump_support_cos c w hsmall he i).2]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · push Not at hX
    obtain ⟨i,hi⟩ := hX
    have hc : ContinuousAt (fun q : DoubleAngularVector N => Real.cos (q.1 i-c.1 i)) u := by fun_prop
    have hn := hc.eventually (Iio_mem_nhds (show Real.cos (u.1 i-c.1 i) < 1/2 by linarith))
    have hz : doublePeriodicizeBump c w =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [hn] with q hq
      by_contra he
      linarith [(doublePeriodicizeBump_support_cos c w hsmall he i).1]
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem doublePeriodicizeBump_eq_on_centeredBox {N : ℕ} (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2)
    {u : DoubleAngularVector N}
    (hx : ∀ i, -Real.pi ≤ u.1 i-c.1 i ∧ u.1 i-c.1 i ≤ Real.pi)
    (hy : ∀ i, -Real.pi ≤ u.2 i-c.2 i ∧ u.2 i-c.2 i ≤ Real.pi) :
    doublePeriodicizeBump c w u = w u := by
  change w (centeredWrap c.1 u.1,centeredWrap c.2 u.2) = w u
  have h1 := periodicizeBump_eq_on_centeredBox c.1 (fun x => w (x,centeredWrap c.2 u.2))
    (fun x hn i => (hsmall (x,centeredWrap c.2 u.2) hn i).1) hx
  change w (centeredWrap c.1 u.1,centeredWrap c.2 u.2) = w (u.1,centeredWrap c.2 u.2) at h1
  rw [h1]
  exact periodicizeBump_eq_on_centeredBox c.2 (fun y => w (u.1,y))
    (fun y hn i => (hsmall (u.1,y) hn i).2) hy

end
end IsingBulk.First
