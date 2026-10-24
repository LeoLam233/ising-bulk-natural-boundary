import IsingBulk.Anisotropic.NegativeCycles.SpatialCutoff
import IsingBulk.First.MeanCoordinates

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First Set Filter Metric
open scoped BigOperators Topology

/-- Full constrained Euclidean radius, including the dependent final angle. -/
def constrainedSquaredRadius {n : ℕ} (q : Fin n→ℝ) : ℝ := squaredRadius (shapeExtend q)

theorem constrainedSquaredRadius_eq {n : ℕ} (q : Fin n→ℝ) :
    constrainedSquaredRadius q=squaredRadius q+(∑i,q i)^2 := by
  unfold constrainedSquaredRadius squaredRadius
  rw [Fin.sum_univ_castSucc]
  simp

theorem constrainedSquaredRadius_nonneg {n : ℕ} (q : Fin n→ℝ) :
    0≤constrainedSquaredRadius q := squaredRadius_nonneg _

theorem constrainedSquaredRadius_contDiff {n : ℕ} (k : ℕ∞) :
    ContDiff ℝ k (@constrainedSquaredRadius n) := by
  have he : @constrainedSquaredRadius n=(fun q => squaredRadius q+(∑i,q i)^2) :=
    funext constrainedSquaredRadius_eq
  rw [he]
  exact (squaredRadius_contDiff k).add (by fun_prop)

def shapeSpatialCutoff {n : ℕ} (b : ContDiffBump (0:ℝ)) (q : Fin n → ℝ) : ℝ :=
  b (constrainedSquaredRadius q)

theorem shapeSpatialCutoff_contDiff {n : ℕ} (b : ContDiffBump (0:ℝ)) (k : ℕ∞) :
    ContDiff ℝ k (@shapeSpatialCutoff n b) := (b.contDiff (n := k)).comp (constrainedSquaredRadius_contDiff k)

theorem shapeSpatialCutoff_one {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : constrainedSquaredRadius q≤b.rIn) : shapeSpatialCutoff b q=1 := by
  apply b.one_of_mem_closedBall
  simpa [Real.dist_eq,abs_of_nonneg (constrainedSquaredRadius_nonneg q)] using hq

theorem shapeSpatialCutoff_zero {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : b.rOut≤constrainedSquaredRadius q) : shapeSpatialCutoff b q=0 := by
  apply b.zero_of_le_dist
  simpa [Real.dist_eq,abs_of_nonneg (constrainedSquaredRadius_nonneg q)] using hq

theorem shapeSpatialCutoff_eventually_one {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : constrainedSquaredRadius q<b.rIn) : shapeSpatialCutoff b=ᶠ[𝓝 q] 1 := by
  have hmem : constrainedSquaredRadius q∈ball (0:ℝ) b.rIn := by
    simpa [Real.dist_eq,abs_of_nonneg (constrainedSquaredRadius_nonneg q)] using hq
  exact (b.eventuallyEq_one_of_mem_ball hmem).comp_tendsto
    ((constrainedSquaredRadius_contDiff (n := n) 0).continuous.tendsto q)

/-- All spatial cutoff derivatives vanish on the fixed inner Euclidean ball. -/
theorem shapeSpatialCutoff_fderiv_eq_zero {n : ℕ} (b : ContDiffBump (0:ℝ)) {q : Fin n → ℝ}
    (hq : constrainedSquaredRadius q<b.rIn) : fderiv ℝ (shapeSpatialCutoff b) q=0 := by
  rw [(shapeSpatialCutoff_eventually_one b hq).fderiv_eq]
  simp

end IsingBulk.Anisotropic.NegativeCycles
