import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import IsingBulk.First.ActualDensityBounds

/-! Constructive fixed smooth cutoffs in arbitrary prescribed local supports.
Only real C∞ regularity is required; no real-analytic cutoff is introduced. -/
namespace IsingBulk.First
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

/-- A compactly supported real cutoff equal to one on a genuine smaller
neighborhood, constructed in any prescribed neighborhood of the center. -/
theorem exists_fixed_smooth_cutoff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (c : E) {U : Set E} (hU : U ∈ 𝓝 c) :
    ∃ chi : E → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧ chi =ᶠ[𝓝 c] (fun _ => 1) ∧ tsupport chi ⊆ U := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  let b : ContDiffBump c := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨b,b.contDiff,b.hasCompactSupport,fun x => ⟨b.nonneg,b.le_one⟩,b.eventuallyEq_one,?_⟩
  rw [b.tsupport_eq]
  intro x hx
  apply hball
  change dist x c < r
  have hx' : dist x c ≤ r/2 := hx
  linarith

/-- A fixed real mean cutoff with a literal hard inner segment and a
separated outer edge. The parameter delta can be chosen below any given bound. -/
theorem exists_fixed_mean_cutoff {D : ℝ} (hD : 0 < D) :
    ∃ delta : ℝ, 0 < delta ∧ delta < D ∧ ∃ eta : ℝ → ℝ,
      ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
      (∀ v, 0 ≤ eta v ∧ eta v ≤ 1) ∧
      (∀ v, |v| ≤ delta/2 → eta v = 1) ∧
      (∀ v, eta v ≠ 0 → |v| < delta) := by
  let delta := D/2
  have hd : 0 < delta := half_pos hD
  let b : ContDiffBump (0:ℝ) := ⟨delta/2,delta,half_pos hd,half_lt_self hd⟩
  refine ⟨delta,hd,half_lt_self hD,b,b.contDiff,b.hasCompactSupport,
    fun v => ⟨b.nonneg,b.le_one⟩,?_,?_⟩
  · intro v hv
    apply b.one_of_mem_closedBall
    simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hv
  · intro v hv
    have hm : v ∈ Function.support b := hv
    rw [b.support_eq] at hm
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hm

/-- Arbitrarily small fixed shape cutoffs are constructed on the actual
zero-sum chart. The source's dependent last coordinate is included in support. -/
theorem exists_fixed_shape_cutoff (n : ℕ) {H : ℝ} (hH : 0 < H)
    {U : Set (Fin n → ℝ)} (hU : U ∈ 𝓝 (0 : Fin n → ℝ)) :
    ∃ chi : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧ chi =ᶠ[𝓝 0] (fun _ => 1) ∧
      tsupport chi ⊆ U ∧ (∀ t ∈ tsupport chi, ∀ j, |shapeExtend t j| < H) := by
  have hcoord : ∀ᶠ t : Fin n → ℝ in 𝓝 0, ∀ j : Fin (n+1), |shapeExtend t j| < H := by
    apply Filter.eventually_all.mpr
    intro j
    have hc := (continuous_shapeExtend_eval j).abs.continuousAt (x := (0 : Fin n → ℝ))
    exact hc.eventually (Iio_mem_nhds (by simpa using hH))
  obtain ⟨chi,hc,hcomp,hr,h1,hs⟩ := exists_fixed_smooth_cutoff (0 : Fin n → ℝ) (Filter.inter_mem hU hcoord)
  exact ⟨chi,hc,hcomp,hr,h1,fun t ht => (hs ht).1,fun t ht => (hs ht).2⟩

end
end IsingBulk.First
