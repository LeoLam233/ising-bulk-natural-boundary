import IsingBulk.Anisotropic.NegativeCycles.CutoffStokes
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter Metric
open scoped BigOperators Topology

/-- Euclidean squared radius, not the dimension-dependent sup-norm cube. -/
def squaredRadius {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, (q i)^2

theorem squaredRadius_nonneg {n : ℕ} (q : Fin n → ℝ) : 0≤squaredRadius q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squaredRadius_contDiff {n : ℕ} (k : ℕ∞) :
    ContDiff ℝ k (@squaredRadius n) := by
  unfold squaredRadius
  fun_prop

def spatialCutoff {n : ℕ} (b : ContDiffBump (0:ℝ)) (q : Fin n → ℝ) : ℝ :=
  b (squaredRadius q)

theorem spatialCutoff_contDiff {n : ℕ} (b : ContDiffBump (0:ℝ)) (k : ℕ∞) :
    ContDiff ℝ k (@spatialCutoff n b) := (b.contDiff (n := k)).comp (squaredRadius_contDiff k)

theorem spatialCutoff_one {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : squaredRadius q≤b.rIn) : spatialCutoff b q=1 := by
  apply b.one_of_mem_closedBall
  simpa [Real.dist_eq,abs_of_nonneg (squaredRadius_nonneg q)] using hq

theorem spatialCutoff_zero {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : b.rOut≤squaredRadius q) : spatialCutoff b q=0 := by
  apply b.zero_of_le_dist
  simpa [Real.dist_eq,abs_of_nonneg (squaredRadius_nonneg q)] using hq

theorem spatialCutoff_eventually_one {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : squaredRadius q<b.rIn) : spatialCutoff b=ᶠ[𝓝 q] 1 := by
  have hmem : squaredRadius q∈ball (0:ℝ) b.rIn := by
    simpa [Real.dist_eq,abs_of_nonneg (squaredRadius_nonneg q)] using hq
  exact (b.eventuallyEq_one_of_mem_ball hmem).comp_tendsto
    ((squaredRadius_contDiff (n := n) 0).continuous.tendsto q)

/-- All spatial cutoff derivatives vanish on the fixed inner Euclidean ball. -/
theorem spatialCutoff_fderiv_eq_zero {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : squaredRadius q<b.rIn) : fderiv ℝ (spatialCutoff b) q=0 := by
  rw [(spatialCutoff_eventually_one b hq).fderiv_eq]
  simp

end IsingBulk.Anisotropic.NegativeCycles
