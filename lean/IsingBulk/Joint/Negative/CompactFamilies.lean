import IsingBulk.Joint.Negative.CurveCoordinates
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Common neighborhoods for genuinely complex parameter families

The compact set is a set of complex parameters, not a set of real ratios.
Analyticity is joint before restriction, and the radius is chosen before the
parameter and before the particle number. These scalar statements supply the
common-neighborhood inputs of the increasing-dimensional argument.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- A compact parameter set contained in an open product neighborhood has a
single transverse radius. The conclusion holds for every point of the compact
set, not merely for a selected parameter. -/
theorem compact_product_tube {X : Type*} [NormedAddCommGroup X]
    {K : Set E} (hK : IsCompact K) {U : Set (X × E)} (hU : IsOpen U)
    (hsub : ∀ eta ∈ K, ((0 : X), eta) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ eta ∈ K, ∀ x : X, ‖x‖ < r → (x, eta) ∈ U := by
  let f : E → X × E := fun eta => (0, eta)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  obtain ⟨r, hr, hthick⟩ := (hK.image hf).exists_cthickening_subset_open hU
    (by rintro _ ⟨eta, heta, rfl⟩; exact hsub eta heta)
  refine ⟨r, hr, ?_⟩
  intro eta heta x hx
  apply hthick
  apply mem_cthickening_of_dist_le (x, eta) (0, eta) r (f '' K)
    (mem_image_of_mem f heta)
  simpa only [Prod.dist_eq, dist_zero_right, dist_self, max_eq_left (norm_nonneg x)] using hx.le

/-- The actual jointly parameterized phase, with the given varying anisotropy. -/
def familyPhase (B : ℂ × E → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (q : (ℂ × ℂ) × E) : ℂ :=
  edgePhase phi hphi ((Real.cos phi : ℂ) + B (q.1.1, q.2) *
    (q.1.1 - 1 + Complex.cos q.1.2))

theorem familyPhase_analyticAt_center (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (eta : E)
    (hB : AnalyticAt ℂ B (0, eta)) :
    AnalyticAt ℂ (familyPhase B phi hphi) ((0, 0), eta) := by
  have hproj : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => (q.1.1, q.2)) ((0, 0), eta) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have ht : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => q.1.1) ((0, 0), eta) :=
    analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => q.1.2) ((0, 0), eta) :=
    analyticAt_snd.comp analyticAt_fst
  have hw : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E =>
      (Real.cos phi : ℂ) + B (q.1.1, q.2) * (q.1.1 - 1 + Complex.cos q.1.2))
      ((0, 0), eta) := analyticAt_const.add ((hB.comp (f := fun q : (ℂ × ℂ) × E => (q.1.1, q.2)) hproj).mul
    ((ht.sub analyticAt_const).add (Complex.analyticAt_cos.comp hd)))
  apply (edgePhase_spec phi hphi).1.comp_of_eq hw
  simp

/-- Uniform joint analyticity on one scalar bidisk for every parameter in a
compact complex family. No pointwise choice of radii appears in the conclusion. -/
theorem compact_family_phase_bidisk (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0, eta)) :
    ∃ r : ℝ, 0 < r ∧ ∀ eta ∈ K, ∀ t d : ℂ, ‖t‖ < r → ‖d‖ < r →
      AnalyticAt ℂ (familyPhase B phi hphi) ((t, d), eta) := by
  obtain ⟨r, hr, hball⟩ := compact_product_tube hK
    (isOpen_analyticAt ℂ (familyPhase B phi hphi))
    (fun eta heta => familyPhase_analyticAt_center B phi hphi eta (hB eta heta))
  exact ⟨r, hr, fun eta heta t d ht hd => hball eta heta (t, d)
    (by simpa only [Prod.norm_def, max_lt_iff] using And.intro ht hd)⟩

/-- The strict lower-half-plane gap and a common bound persist on a single
parameter disk for every member of a compact admissible holomorphic family. -/
theorem compact_family_anisotropy_bounds (B : ℂ × E → ℂ) {K : Set E}
    (hK : IsCompact K) (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0, eta))
    {beta : ℝ} (hbeta : 0 < beta) (hgap : ∀ eta ∈ K, (B (0, eta)).im ≤ -beta) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ eta ∈ K, ∀ t : ℂ, ‖t‖ < r →
      AnalyticAt ℂ B (t, eta) ∧ (B (t, eta)).im < -beta / 2 ∧
        B (t, eta) ≠ 0 ∧ ‖B (t, eta)‖ < M := by
  have hcont : ContinuousOn (fun eta => B (0, eta)) K := by
    intro eta heta
    exact ((hB eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  let M := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right C 0]
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ B q ∧ (B q).im < -beta / 2 ∧ ‖B q‖ < M}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      (((Complex.continuous_im.continuousAt.comp hq.1.continuousAt).eventually_lt
        continuousAt_const hq.2.1).and
        (hq.1.continuousAt.norm.eventually_lt continuousAt_const hq.2.2))
  obtain ⟨r, hr, htube⟩ := compact_product_tube hK hU (by
    intro eta heta
    refine ⟨hB eta heta, ?_, ?_⟩
    · linarith [hgap eta heta]
    · dsimp [M]; linarith [hC eta heta, le_max_left C 0])
  refine ⟨r, M, hr, hM, ?_⟩
  intro eta heta t ht
  obtain ⟨ha, him, hnorm⟩ := htube eta heta t ht
  refine ⟨ha, him, ?_, hnorm⟩
  intro hz
  simp only [hz, Complex.zero_im] at him
  linarith

end
end IsingBulk.Joint.Negative
