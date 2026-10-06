import IsingBulk.Tail.NestedSectorPartition
import IsingBulk.Tail.ScaledCutoffJets
import IsingBulk.Tail.GlobalGeometry
import IsingBulk.Tail.SelectorCutoffs
import IsingBulk.Tail.ScaleInclusions

/-! Fixed microcore-complement anchors and a smooth squared-shape split.
Every real cutoff jet retains the same closed geometric support. -/
namespace IsingBulk.Tail
noncomputable section
open Set Function IsingBulk.Jets
open scoped BigOperators ContDiff Topology

def microExteriorAnchor {N : ℕ} (b : ℝ) (q : Fin N) (u : Fin N → ℝ) : ℝ :=
  outerAnchor (finiteExtension (fun i => microCutoffBase (u i/b))) q

theorem microExteriorAnchor_telescope {N : ℕ} (b : ℝ) (u : Fin N → ℝ) :
    scaledMicroCutoff N b u + ∑ q : Fin N, microExteriorAnchor b q u = 1 := by
  have h := outerAnchor_telescope (finiteExtension (fun i => microCutoffBase (u i/b))) N
  rw [← Fin.prod_univ_eq_prod_range, ← Fin.sum_univ_eq_sum_range] at h
  simpa only [finiteExtension_fin,scaledMicroCutoff,microExteriorAnchor] using h

theorem microExteriorAnchor_smooth {N : ℕ} (b : ℝ) (q : Fin N) :
    ContDiff ℝ ∞ (microExteriorAnchor b q) := by
  have hc (i : ℕ) : ContDiff ℝ ∞ (fun u : Fin N → ℝ =>
      finiteExtension (fun j => microCutoffBase (u j/b)) i) := by
    by_cases hi : i < N
    · simp only [finiteExtension,dite_eq_left hi]
      exact (fixedBranchBump 1 (by norm_num)).contDiff.comp
        ((contDiff_apply ℝ ℝ (⟨i,hi⟩ : Fin N)).div_const b)
    · simp only [finiteExtension,dite_eq_right hi]
      exact contDiff_const
  exact (contDiff_const.sub (hc q)).mul (contDiff_prod (fun i _ => hc i))

theorem microExteriorAnchor_jet_support {N : ℕ} {b : ℝ} (hb : 0 < b)
    (q : Fin N) (l : List (Fin N)) :
    tsupport (cutoffJet l (microExteriorAnchor b q)) ⊆ {u | b/2 ≤ |u q|} := by
  apply (cutoffJet_tsupport_subset l _).trans
  apply closure_minimal
  · intro u hu
    have hn := outerAnchor_ne_zero
      (finiteExtension (fun i => microCutoffBase (u i/b))) q hu
    rw [finiteExtension_fin] at hn
    by_contra h
    change ¬ b/2 ≤ |u q| at h
    have hh : |u q/b| ≤ 1/2 := by
      rw [abs_div,abs_of_pos hb]
      exact (div_le_iff₀ hb).mpr (by linarith [lt_of_not_ge h])
    exact hn (fixedBranchBump_one 1 (by norm_num) hh)
  · exact isClosed_le continuous_const ((continuous_apply q).abs)

def branchShapeSquare {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  ∑ i, (u i-branchMean u)^2

theorem branchShapeSquare_smooth (N : ℕ) : ContDiff ℝ ∞ (@branchShapeSquare N) := by
  unfold branchShapeSquare branchMean
  fun_prop

theorem branchShapeSquare_eq {N : ℕ} (u : Fin N → ℝ) :
    branchShapeSquare u = (branchShapeRadius u)^2 := by
  exact (Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).symm

def branchFarCutoff {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) : ℝ :=
  thresholdStep (rho^2) (4*rho^2) (branchShapeSquare u)
def branchNearCutoff {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) : ℝ :=
  1-branchFarCutoff rho u

theorem branch_shape_split {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) :
    branchNearCutoff rho u + branchFarCutoff rho u = 1 := by
  unfold branchNearCutoff; ring

theorem branch_shape_cutoffs_smooth {N : ℕ} (rho : ℝ) :
    ContDiff ℝ ∞ (@branchFarCutoff N rho) ∧ ContDiff ℝ ∞ (@branchNearCutoff N rho) := by
  have hh : ContDiff ℝ ∞ (@branchFarCutoff N rho) := by
    unfold branchFarCutoff thresholdStep
    exact Real.smoothTransition.contDiff.comp
      (((branchShapeSquare_smooth N).sub contDiff_const).div_const _)
  exact ⟨hh,contDiff_const.sub hh⟩

theorem branch_far_jet_support {N : ℕ} {rho : ℝ} (hr : 0 < rho)
    (l : List (Fin N)) :
    tsupport (cutoffJet l (branchFarCutoff rho)) ⊆ {u | rho ≤ branchShapeRadius u} := by
  apply (cutoffJet_tsupport_subset l _).trans
  apply closure_minimal
  · intro u hu
    by_contra h
    change ¬ rho ≤ branchShapeRadius u at h
    have hh : branchShapeSquare u ≤ rho^2 := by
      rw [branchShapeSquare_eq]
      have hn := Real.sqrt_nonneg (∑ i, (u i-branchMean u)^2)
      change 0 ≤ branchShapeRadius u at hn
      nlinarith [lt_of_not_ge h]
    exact hu (thresholdStep_zero (by nlinarith [sq_pos_of_pos hr]) hh)
  · apply isClosed_le continuous_const
    unfold branchShapeRadius branchMean
    fun_prop

theorem branch_near_jet_support {N : ℕ} {rho : ℝ} (hr : 0 < rho)
    (l : List (Fin N)) :
    tsupport (cutoffJet l (branchNearCutoff rho)) ⊆ {u | branchShapeRadius u ≤ 2*rho} := by
  apply (cutoffJet_tsupport_subset l _).trans
  apply closure_minimal
  · intro u hu
    by_contra h
    change ¬ branchShapeRadius u ≤ 2*rho at h
    have hh : 4*rho^2 ≤ branchShapeSquare u := by
      rw [branchShapeSquare_eq]
      nlinarith [lt_of_not_ge h]
    have he := thresholdStep_one (l := rho^2) (h := 4*rho^2) (by nlinarith [sq_pos_of_pos hr]) hh
    exact hu (by change 1-thresholdStep _ _ _ = 0; rw [he]; ring)
  · apply isClosed_le _ continuous_const
    unfold branchShapeRadius branchMean
    fun_prop


def microExteriorNearWeight {N : ℕ} (b rho : ℝ) (q : Fin N) (u : Fin N → ℝ) : ℝ :=
  microExteriorAnchor b q u * branchNearCutoff rho u

def microExteriorFarWeight {N : ℕ} (b rho : ℝ) (q : Fin N) (u : Fin N → ℝ) : ℝ :=
  microExteriorAnchor b q u * branchFarCutoff rho u

theorem microExterior_full_partition {N : ℕ} (b rho : ℝ) (u : Fin N → ℝ) :
    scaledMicroCutoff N b u +
      ∑ q : Fin N, (microExteriorNearWeight b rho q u + microExteriorFarWeight b rho q u) = 1 := by
  have he (q : Fin N) : microExteriorNearWeight b rho q u + microExteriorFarWeight b rho q u =
      microExteriorAnchor b q u := by
    unfold microExteriorNearWeight microExteriorFarWeight
    rw [← mul_add,branch_shape_split,mul_one]
  simp only [he]
  exact microExteriorAnchor_telescope b u

theorem microExteriorNear_jet_common_sign {A c B : ℝ} (hc : 0 < c)
    (hB : allBranchScaleThreshold A c ≤ B) {N : ℕ} (hN : 1 ≤ N)
    (q : Fin N) (l : List (Fin N)) (u : Fin N → ℝ)
    (hu : u ∈ tsupport (cutoffJet l
      (microExteriorNearWeight (allBranchMicroRadius A c N) (allBranchEqualityRadius B N) q))) :
    (3*allBranchMicroRadius A c N/8 ≤ branchMean u ∧
      ∀ i, allBranchMicroRadius A c N/4 ≤ u i) ∨
    (branchMean u ≤ -(3*allBranchMicroRadius A c N/8) ∧
      ∀ i, u i ≤ -(allBranchMicroRadius A c N/4)) := by
  have hs := cutoffJet_tsupport_subset l _ hu
  have ha : u ∈ tsupport (microExteriorAnchor (allBranchMicroRadius A c N) q) :=
    tsupport_mul_subset_left hs
  have hn : u ∈ tsupport (branchNearCutoff (allBranchEqualityRadius B N)) :=
    tsupport_mul_subset_right hs
  have hb : 0 < allBranchMicroRadius A c N := by
    unfold allBranchMicroRadius
    have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hr : 0 < allBranchEqualityRadius B N := Real.exp_pos _
  have ha' := microExteriorAnchor_jet_support hb q [] ha
  have hn' := branch_near_jet_support hr [] hn
  exact all_branch_near_scale_common_sign hc hB hN u q ha' hn'

end
end IsingBulk.Tail
