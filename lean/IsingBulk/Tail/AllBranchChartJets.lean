import IsingBulk.Tail.AllBranchAngleBoxChart
import IsingBulk.Tail.AnchoredCutoffJets

/-! The fixed compact lower chart and outer branch cutoffs have uniform
C_J^N real-coordinate jet cost, before the dimension N is chosen. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Function
open scoped BigOperators Topology ContDiff

def branchChartScalar (b delta h : ℝ) (hd : 0 < delta) (u : ℝ) : ℝ :=
  microCutoffBase (u/h)*sectorBranch b delta hd (u-b)

theorem branchChartScalar_smooth (b delta h : ℝ) (hd : 0 < delta) :
    ContDiff ℝ ∞ (branchChartScalar b delta h hd) :=
  ((fixedBranchBump 1 (by norm_num)).contDiff.comp (contDiff_id.div_const h)).mul
    ((sector_labels_smooth b delta hd).2.2.comp (contDiff_id.sub contDiff_const))

theorem branchChartScalar_iterated_support (b delta h : ℝ) (hd : 0 < delta) (hh : 0 < h) (k : ℕ) :
    tsupport (iteratedDeriv k (branchChartScalar b delta h hd)) ⊆ Icc (-h) h := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero]
    apply closure_minimal _ isClosed_Icc
    intro u hu
    have hchi : microCutoffBase (u/h) ≠ 0 := (mul_ne_zero_iff.mp hu).1
    have hab := fixedBranchBump_support 1 (by norm_num) hchi
    rw [abs_div,abs_of_pos hh] at hab
    have hu' : |u|<h := by have := (div_lt_iff₀ hh).mp hab; linarith
    exact ⟨(abs_lt.mp hu').1.le,(abs_lt.mp hu').2.le⟩
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem branchChartScalar_jets_bounded (b delta h : ℝ) (hd : 0 < delta) (hh : 0 < h) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, k ≤ J → ∀ u : ℝ,
      ‖iteratedDeriv k (branchChartScalar b delta h hd) u‖ ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, ∀ u : ℝ, ‖iteratedDeriv k (branchChartScalar b delta h hd) u‖ ≤ C := by
    have hc := (branchChartScalar_smooth b delta h hd).continuous_iteratedDeriv k (by simp)
    have hs : HasCompactSupport (iteratedDeriv k (branchChartScalar b delta h hd)) :=
      isCompact_Icc.of_isClosed_subset isClosed_closure (branchChartScalar_iterated_support b delta h hd hh k)
    exact hc.bounded_above_of_compact_support hs
  induction J with
  | zero =>
    obtain ⟨C,hC⟩ := hb 0
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro k hk u
    have he : k=0 := by omega
    exact he ▸ (hC u).trans (le_max_right _ _)
  | succ J ih =>
    obtain ⟨C,hC,hprev⟩ := ih
    obtain ⟨D,hD⟩ := hb (J+1)
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro k hk u
    by_cases hkJ : k≤J
    · exact (hprev k hkJ u).trans (le_max_left _ _)
    · have he : k=J+1 := by omega
      exact he ▸ (hD u).trans (le_max_right _ _)

theorem allBranchChartWeight_product {N : ℕ} (b eta alpha delta h : ℝ) (hd : 0 < delta)
    (_hb : 0 < b) (_hbpi : b < Real.pi) (halpha : 0 < alpha) (hh : 0 < h)
    (hhb : h ≤ b/2) (hhpi : h ≤ (Real.pi-b)/2) (u : Fin N → ℝ) :
    allBranchChartWeight N b eta alpha delta h hd u = ∏ i, branchChartScalar b delta h hd (u i) := by
  have hsel : scaledMicroCutoff N h u*angularSelector (constructedSelector b eta alpha) (fun i => u i-b)=
      scaledMicroCutoff N h u := by
    by_cases hz : scaledMicroCutoff N h u=0
    · rw [hz,zero_mul]
    · have hu := scaledMicroCutoff_jet_tsupport hh [] (subset_closure hz)
      have ha : ∀ i, (constructedSelector b eta alpha).a (u i-b)=0 := by
        intro i
        have hui := abs_le.mp (hu i)
        have hangle : -Real.pi < u i-b ∧ u i-b < 0 := by constructor <;> linarith
        have hsin := Real.sin_neg_of_neg_of_neg_pi_lt hangle.2 hangle.1
        exact thresholdStep_zero (by linarith) (by linarith)
      have he : angularSelector (constructedSelector b eta alpha) (fun i => u i-b)=1 := by
        simp [angularSelector,selectorWeight,ha]
      rw [he,mul_one]
  unfold allBranchChartWeight
  rw [hsel]
  simp only [branchChartScalar,Finset.prod_mul_distrib,scaledMicroCutoff]

theorem allBranchChartWeight_jet_bound (b eta alpha delta h : ℝ) (hd : 0 < delta)
    (hb : 0 < b) (hbpi : b < Real.pi) (halpha : 0 < alpha) (hh : 0 < h)
    (hhb : h ≤ b/2) (hhpi : h ≤ (Real.pi-b)/2) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ l : List (Fin N), l.length ≤ J → ∀ u : Fin N → ℝ,
      ‖cutoffJet l (allBranchChartWeight N b eta alpha delta h hd) u‖ ≤ C^N := by
  obtain ⟨C,hC,hjets⟩ := branchChartScalar_jets_bounded b delta h hd hh J
  refine ⟨C,hC,?_⟩
  intro N l hl u
  have he : allBranchChartWeight N b eta alpha delta h hd =
      fun x => ∏ i, branchChartScalar b delta h hd (x i) :=
    funext (allBranchChartWeight_product b eta alpha delta h hd hb hbpi halpha hh hhb hhpi)
  rw [he]
  have hg (i : Fin N) (k : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv k (branchChartScalar b delta h hd))
        (iteratedDeriv (k+1) (branchChartScalar b delta h hd) x) x := by
    have hd' := (branchChartScalar_smooth b delta h hd).differentiable_iteratedDeriv k
      (by exact_mod_cast (ENat.natCast_lt_top k)) x
    simpa only [iteratedDeriv_succ] using hd'.hasDerivAt
  have hj := coordinateProduct_word_jet (fun _ : Fin N => fun k => iteratedDeriv k (branchChartScalar b delta h hd)) hg l u
  simp only [iteratedDeriv_zero] at hj
  rw [hj,norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => hjets _ (List.count_le_length.trans hl) _)
    _ = _ := by simp

end
end IsingBulk.Tail
