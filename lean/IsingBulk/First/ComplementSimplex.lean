import IsingBulk.First.ComplementPhaseSum
import Mathlib.Topology.Order.Compact

/-! Compact normalization of the positive auxiliary cone and an actual local
nonstationary margin instantiated from the selected prime-family classification. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped BigOperators Topology

/-- Source auxiliary directions have nonnegative coordinates summing to one. -/
def auxiliarySimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {η | (∀ i, 0 ≤ η i) ∧ ∑ i, η i = 1}

theorem auxiliarySimplex_isCompact (ι : Type*) [Fintype ι] :
    IsCompact (auxiliarySimplex ι) := by
  have hpos : IsClosed {η : ι → ℝ | ∀ i, 0 ≤ η i} := by
    have h (i : ι) : IsClosed {η : ι → ℝ | (0 : ℝ) ≤ η i} := isClosed_le continuous_const (continuous_apply i)
    convert isClosed_iInter h using 1
    ext η
    simp
  have hsum : IsClosed {η : ι → ℝ | ∑ i, η i = 1} := isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed (auxiliarySimplex ι) := hpos.inter hsum
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : ι → ℝ) 1) isCompact_Icc hc
  intro η hη
  refine ⟨hη.1, ?_⟩
  intro i
  have h := Finset.single_le_sum (fun j _ => hη.1 j) (Finset.mem_univ i)
  simpa only [hη.2, Pi.one_apply] using h

/-- Every nonzero positive auxiliary vector lies on a ray through this compact simplex. -/
theorem normalized_auxiliary_mem_simplex {ι : Type*} [Fintype ι]
    (ξ : ι → ℝ) (hξ : ∀ i, 0 ≤ ξ i) (hR : 0 < ∑ i, ξ i) :
    (fun i => ξ i / ∑ j, ξ j) ∈ auxiliarySimplex ι := by
  refine ⟨fun i => div_nonneg (hξ i) hR.le, ?_⟩
  rw [← Finset.sum_div, div_self (ne_of_gt hR)]

/-- The actual source phase has a uniform nonstationary direction on a fixed
angular neighborhood, simultaneously for the whole normalized auxiliary simplex. -/
theorem selected_source_local_direction_margin {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y) :
    ∃ (e : DoubleAngularVector (2*p)) (δ ρ : ℝ), 0 < δ ∧ 0 < ρ ∧
      ∀ {ι : Type} [Fintype ι] (J : ι → SingularFactorIndex (2*p)),
      (∀ i, singularFactorActive x y (2*PrimeFamily.cosineAverage p a b) (J i)) →
      ∀ (r : ℝ) (s : ℂ) (u : DoubleAngularVector (2*p)) (η : ι → ℝ),
      |r-1| < ρ → ‖u‖ < ρ → η ∈ auxiliarySimplex ι →
      δ ≤ ‖phaseDirection e (sourcePhaseSum r s x y J η) u‖ := by
  obtain ⟨e, δ, hδ, he⟩ := selected_active_uniform_separator hp hp11 ha hb hx hy hgood
  have hmap : ContinuousAt (fun q : ℝ × DoubleAngularVector (2*p) =>
      (q.1, torusShift x q.2.1, torusShift y q.2.2)) (1, 0) := by
    unfold torusShift angularCurve
    fun_prop
  have ht : Tendsto (fun q : ℝ × DoubleAngularVector (2*p) =>
      (q.1, torusShift x q.2.1, torusShift y q.2.2)) (𝓝 (1, 0)) (𝓝 (1, x, y)) := by
    have hx0 : torusShift x 0 = x := by funext i; simp [torusShift, angularCurve]
    have hy0 : torusShift y 0 = y := by funext i; simp [torusShift, angularCurve]
    simpa only [Prod.fst_zero, Prod.snd_zero, hx0, hy0] using hmap.tendsto
  have he' := ht.eventually he
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp he'
  refine ⟨e, δ, min ρ (1/2), hδ, lt_min hρ (by norm_num), ?_⟩
  intro ι _ J hJ r s u η hr hu hη
  have hrc : r ≠ 0 := by
    have hsmall := lt_of_lt_of_le hr (min_le_right ρ (1/2))
    have hh := (abs_lt.mp hsmall).1
    linarith
  have hpt : dist (r, u) (1, (0 : DoubleAngularVector (2*p))) < ρ := by
    simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using
      And.intro (lt_of_lt_of_le hr (min_le_left _ _)) (lt_of_lt_of_le hu (min_le_left _ _))
  have hsep := hball hpt
  have hdir := sourcePhaseSum_direction_margin r hrc s x y hx hy J η hη.1 hη.2 u e
    (fun i => (hsep (J i) (hJ i)).le)
  exact hdir.trans (Complex.im_le_norm _)

end
end IsingBulk.First
