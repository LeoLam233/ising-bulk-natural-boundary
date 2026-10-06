import IsingBulk.First.MeanParameterIntegral

/-! Compact integrals of a jointly analytic source family, including a fixed
real-variable weight. The weight is never analytically continued. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_weighted_compact_integral_iteratedDeriv
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ × E → ℂ) (u : ℝ → E) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : ContinuousOn w K)
    (ha : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,u x))
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖meanParameterIter F j (s,u x)‖ ≤ C)
    (j : ℕ) (s : ℂ) (hs : s ∈ U) :
    (deriv^[j] (fun z => ∫ x in K, w x * F (z,u x))) s =
      ∫ x in K, w x * meanParameterIter F j (s,u x) := by
  let H : ℕ → ℂ → ℝ → ℂ := fun j s x => w x * meanParameterIter F j (s,u x)
  have hc : ∀ j s, s ∈ U → ContinuousOn (H j s) K := by
    intro j s hs x hx
    apply (hw x hx).mul
    exact ((meanParameterIter_analyticAt (ha s hs x hx) j).continuousAt.comp (f := fun y : ℝ => (s,u y))
      (continuous_const.prodMk hu).continuousAt).continuousWithinAt
  have hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s := by
    intro j s hs x hx
    have hh := meanParameterIter_analyticAt (ha s hs x hx) j
    have has : AnalyticAt ℂ (fun z : ℂ => meanParameterIter F j (z,u x)) s :=
      hh.comp (f := fun z : ℂ => (z,u x)) (analyticAt_id.prod analyticAt_const)
    exact has.differentiableAt.hasDerivAt.const_mul (w x)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hw
  have hbH : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖H j s x‖ ≤ C := by
    intro j
    obtain ⟨C,hC⟩ := hb j
    refine ⟨max M 0*C,?_⟩
    intro s hs x hx
    change ‖w x * meanParameterIter F j (s,u x)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((hM x hx).trans (le_max_left _ _)) (hC s hs x hx)
      (norm_nonneg _) (le_max_right _ _)
  exact compact_parameter_integral_iteratedDeriv hK hU H hc hd hbH j s hs

theorem analytic_weighted_compact_integral_hasDerivAt
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ × E → ℂ) (u : ℝ → E) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : ContinuousOn w K)
    (ha : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,u x))
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖meanParameterIter F j (s,u x)‖ ≤ C)
    (j : ℕ) (s : ℂ) (hs : s ∈ U) :
    HasDerivAt (fun z => ∫ x in K, w x * meanParameterIter F j (z,u x))
      (∫ x in K, w x * meanParameterIter F (j+1) (s,u x)) s := by
  let H : ℕ → ℂ → ℝ → ℂ := fun j s x => w x * meanParameterIter F j (s,u x)
  have hc : ∀ j s, s ∈ U → ContinuousOn (H j s) K := by
    intro j s hs x hx
    apply (hw x hx).mul
    exact ((meanParameterIter_analyticAt (ha s hs x hx) j).continuousAt.comp (f := fun y : ℝ => (s,u y))
      (continuous_const.prodMk hu).continuousAt).continuousWithinAt
  have hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s := by
    intro j s hs x hx
    have hh := meanParameterIter_analyticAt (ha s hs x hx) j
    have has : AnalyticAt ℂ (fun z : ℂ => meanParameterIter F j (z,u x)) s :=
      hh.comp (f := fun z : ℂ => (z,u x)) (analyticAt_id.prod analyticAt_const)
    exact has.differentiableAt.hasDerivAt.const_mul (w x)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hw
  have hbH : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖H j s x‖ ≤ C := by
    intro j
    obtain ⟨C,hC⟩ := hb j
    refine ⟨max M 0*C,?_⟩
    intro s hs x hx
    change ‖w x * meanParameterIter F j (s,u x)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((hM x hx).trans (le_max_left _ _)) (hC s hs x hx)
      (norm_nonneg _) (le_max_right _ _)
  exact compact_parameter_integral_hasDerivAt hK hU H hc hd hbH j s hs

theorem analytic_weighted_compact_integral_analyticAt
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ × E → ℂ) (u : ℝ → E) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : ContinuousOn w K)
    (ha : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,u x))
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖meanParameterIter F j (s,u x)‖ ≤ C)
    (s : ℂ) (hs : s ∈ U) : AnalyticAt ℂ (fun z => ∫ x in K, w x * F (z,u x)) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hU.mem_nhds hs] with z hz
  exact (analytic_weighted_compact_integral_hasDerivAt hK hU F u hu w hw ha hb 0 z hz).differentiableAt

/-- Uniform compact-integral bounds apply to the actual iterated derivative
of the integral, after the preceding interchange theorem. -/
theorem analytic_weighted_compact_integral_bounds
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ × E → ℂ) (u : ℝ → E) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : ContinuousOn w K)
    (ha : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,u x))
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖meanParameterIter F j (s,u x)‖ ≤ C) :
    ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ U,
      ‖(deriv^[j] (fun z => ∫ x in K, w x * F (z,u x))) s‖ ≤ C := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hw
  intro j
  obtain ⟨C,hC⟩ := hb j
  let B := max M 0 * max C 0 * volume.real K
  refine ⟨B+1,by dsimp [B]; positivity,?_⟩
  intro s hs
  rw [analytic_weighted_compact_integral_iteratedDeriv hK hU F u hu w hw ha hb j s hs]
  apply (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top ?_).trans
    (show B ≤ B+1 by linarith)
  intro x hx
  rw [norm_mul]
  exact mul_le_mul ((hM x hx).trans (le_max_left _ _))
    ((hC s hs x hx).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

end
end IsingBulk.First
