import IsingBulk.Tail.PartitionAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Constructed source-sized smooth branch bumps and anchor-jet supports.
The periodic left/right seam and source slope separation remain separate. -/
namespace IsingBulk.Tail
noncomputable section
open Set
open scoped BigOperators ContDiff

def fixedBranchBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0:ℝ) :=
  ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩

theorem fixedBranchBump_one (δ : ℝ) (hδ : 0 < δ) {u : ℝ} (hu : |u| ≤ δ/2) :
    fixedBranchBump δ hδ u = 1 := by
  apply (fixedBranchBump δ hδ).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,fixedBranchBump] using hu

theorem fixedBranchBump_support (δ : ℝ) (hδ : 0 < δ) {u : ℝ}
    (hu : fixedBranchBump δ hδ u ≠ 0) : |u| < δ := by
  have hh : u ∈ Function.support (fixedBranchBump δ hδ) := hu
  rw [(fixedBranchBump δ hδ).support_eq] at hh
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,fixedBranchBump] using hh

def branchAnchorWeight {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (q : Fin N)
    (u : Fin N → ℝ) : ℝ :=
  (1-fixedBranchBump δ hδ (u q)) *
    ∏ i ∈ Finset.univ.filter (fun i : Fin N => i < q), fixedBranchBump δ hδ (u i)

theorem branchAnchorWeight_smooth {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (q : Fin N) :
    ContDiff ℝ ∞ (branchAnchorWeight δ hδ q) := by
  unfold branchAnchorWeight
  apply ContDiff.mul
  · exact contDiff_const.sub ((fixedBranchBump δ hδ).contDiff.comp (contDiff_apply ℝ ℝ q))
  · apply contDiff_prod
    intro i _
    exact (fixedBranchBump δ hδ).contDiff.comp (contDiff_apply ℝ ℝ i)

theorem branchAnchorWeight_support {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (q : Fin N) :
    Function.support (branchAnchorWeight δ hδ q) ⊆ {u | δ/2 ≤ |u q|} := by
  intro u hu
  change branchAnchorWeight δ hδ q u ≠ 0 at hu
  by_contra hn
  have hlt : |u q| < δ/2 := lt_of_not_ge hn
  have he := fixedBranchBump_one δ hδ hlt.le
  simp [branchAnchorWeight,he] at hu

/-- Every finite jet of the constructed anchor retains |u_q|≥δ/2. -/
theorem branchAnchorWeight_jet_support {N : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (q : Fin N) (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j (branchAnchorWeight δ hδ q)) ⊆ {u | δ/2 ≤ |u q|} := by
  apply finite_jet_retains_closed_support
  · exact isClosed_le continuous_const ((continuous_apply q).abs)
  · exact branchAnchorWeight_support δ hδ q

/-- The inner source scale is fixed before ε and N. Its support lies within
δ/L², strictly inside the outer plateau when L>2. -/
theorem inner_branch_scale (δ L : ℝ) (hδ : 0 < δ) (hL : 2 < L) :
    0 < δ/(2*L^2) ∧ 2*(δ/(2*L^2)) < δ/2 := by
  constructor
  · positivity
  · have hsq : 4 < L^2 := by nlinarith
    have hp : 0 < L^2 := by positivity
    have he : 2*(δ/(2*L^2))=δ/L^2 := by ring
    rw [he]
    apply (div_lt_iff₀ hp).mpr
    nlinarith

end
end IsingBulk.Tail
