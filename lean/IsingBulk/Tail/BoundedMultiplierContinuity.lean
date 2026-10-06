import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace IsingBulk.Tail
open Filter
open scoped Topology

/-- A locally bounded scalar need not be continuous at a zero of the continuous factor. -/
theorem continuousAt_bounded_smul_zero {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : X → ℝ) (f : X → E) (x : X)
    (hf : ContinuousAt f x) (hz : f x = 0)
    (hg : ∀ᶠ y in 𝓝 x, ‖g y‖ ≤ 1) : ContinuousAt (fun y => g y • f y) x := by
  have hlim : Tendsto (fun y => ‖f y‖) (𝓝 x) (𝓝 0) := by
    simpa [ContinuousAt, hz] using hf.norm
  have hzero : Tendsto (fun y => g y • f y) (𝓝 x) (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hg] with y hy
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_eq (one_mul _)
  simpa [ContinuousAt, hz] using hzero

end IsingBulk.Tail
