import IsingBulk.First.ComplementFubini
import Mathlib.Topology.Order.Compact

/-! Explicit integrable exponential domination on a noncompact positive
auxiliary orthant. The constants depend on the fixed compact parameter set;
no boundary-uniform or radius-uniform majorant is asserted. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem compact_finite_negative_margin {P ι : Type*} [TopologicalSpace P] [Fintype ι]
    {K : Set P} (hK : IsCompact K) (d : ι → P → ℝ)
    (hd : ∀ i, ContinuousOn (d i) K) (hneg : ∀ i p, p ∈ K → d i p < 0) :
    ∃ δ > 0, ∀ i p, p ∈ K → d i p ≤ -δ := by
  classical
  have hi (i : ι) : ∃ δ > 0, ∀ p ∈ K, d i p ≤ -δ := by
    by_cases hn : K.Nonempty
    · obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hn (hd i)
      refine ⟨-d i p, neg_pos.mpr (hneg i p hp), ?_⟩
      intro q hq
      simpa only [neg_neg] using (show d i q ≤ d i p from hmax hq)
    · exact ⟨1, by norm_num, fun p hp => False.elim (hn ⟨p,hp⟩)⟩
  have hf (T : Finset ι) : ∃ δ > 0, ∀ i ∈ T, ∀ p ∈ K, d i p ≤ -δ := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i T _ ih =>
      obtain ⟨δ,hδ,hδb⟩ := hi i
      obtain ⟨η,hη,hηb⟩ := ih
      refine ⟨min δ η, lt_min hδ hη, ?_⟩
      intro j hj p hp
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hδb p hp).trans (neg_le_neg (min_le_left _ _))
      · exact (hηb j hj p hp).trans (neg_le_neg (min_le_right _ _))
  obtain ⟨δ,hδ,hb⟩ := hf Finset.univ
  exact ⟨δ,hδ,fun i p hp => hb i (Finset.mem_univ _) p hp⟩

theorem norm_exponential_sum_le {ι : Type*} [Fintype ι] (d : ι → ℂ) (δ : ℝ)
    (hd : ∀ i, (d i).re ≤ -δ) (ξ : ι → ℝ) (hξ : ∀ i, 0 ≤ ξ i) :
    ‖Complex.exp (∑ i, d i*(ξ i:ℂ))‖ ≤
      ‖Complex.exp (∑ i, (-δ:ℂ)*(ξ i:ℂ))‖ := by
  simp only [Complex.norm_exp, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
  apply Real.exp_le_exp.mpr
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hd i) (hξ i))

variable {P E ι : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  [Fintype ι]

theorem compact_parameter_auxiliary_dominator {C : Set P} {K : Set E}
    (hC : IsCompact C) (hK : IsCompact K) (A : P → E → ℂ) (d : ι → P → E → ℂ)
    (hA : ContinuousOn (fun p : P × E => A p.1 p.2) (C ×ˢ K))
    (hd : ∀ i, ContinuousOn (fun p : P × E => d i p.1 p.2) (C ×ˢ K))
    (hneg : ∀ i t, t ∈ C → ∀ u ∈ K, (d i t u).re < 0)
    (hzero : ∀ t ∈ C, ∀ u ∉ K, A t u = 0) :
    ∃ b : E × (ι → ℝ) → ℝ,
      Integrable b (μ.prod (volume.restrict (positiveAuxiliaryOrthant ι))) ∧
      ∀ t ∈ C, ∀ p : E × (ι → ℝ), p.2 ∈ positiveAuxiliaryOrthant ι →
        ‖A t p.1*Complex.exp (∑ i, d i t p.1*(p.2 i:ℂ))‖ ≤ b p := by
  obtain ⟨δ,hδ,hδb⟩ := compact_finite_negative_margin (hC.prod hK)
    (fun i p => (d i p.1 p.2).re)
    (fun i => Complex.continuous_re.comp_continuousOn (hd i))
    (fun i p hp => hneg i p.1 hp.1 p.2 hp.2)
  obtain ⟨M,hM⟩ := (hC.prod hK).exists_bound_of_continuousOn hA
  let B : E → ℝ := K.indicator (fun _ => max M 0)
  let D : (ι → ℝ) → ℝ := fun ξ => ‖Complex.exp (∑ i, (-δ:ℂ)*(ξ i:ℂ))‖
  have hBi : Integrable B μ :=
    (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (C := max M 0) hK.measure_lt_top.ne)
  have hDi : Integrable D (volume.restrict (positiveAuxiliaryOrthant ι)) :=
    (auxiliary_exponential_integrable (fun _ : ι => (-δ:ℂ)) (fun _ => by simpa using neg_neg_of_pos hδ)).norm
  refine ⟨fun p => B p.1*D p.2, hBi.mul_prod hDi, ?_⟩
  intro t ht p hp
  by_cases hu : p.1 ∈ K
  · have hbA : ‖A t p.1‖ ≤ max M 0 := (hM (t,p.1) ⟨ht,hu⟩).trans (le_max_left _ _)
    have hbexp := norm_exponential_sum_le (fun i => d i t p.1) δ
      (fun i => hδb i (t,p.1) ⟨ht,hu⟩) p.2 (fun i => (hp i (Set.mem_univ i)).le)
    simp only [B, Set.indicator_of_mem hu, norm_mul]
    exact mul_le_mul hbA hbexp (norm_nonneg _) (le_max_right _ _)
  · rw [hzero t ht p.1 hu, zero_mul, norm_zero]
    simp only [B, Set.indicator_of_notMem hu, zero_mul, le_refl]

end
end IsingBulk.First
