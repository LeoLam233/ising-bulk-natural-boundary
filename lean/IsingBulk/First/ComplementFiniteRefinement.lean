import IsingBulk.First.FiniteTorusRefinement
import IsingBulk.First.ComplementLocalFormFactor

/-! Finite refinement of the actual selected-point complementary weight,
with every chart radius and every local bound constructed from the source. -/
namespace IsingBulk.First
noncomputable section
open Set Metric
open scoped Topology ContDiff BigOperators

private theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨e,he,hb⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) e,lt_min (hf i (Finset.mem_insert_self _ _)) he,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

/-- A true finite partition into local lifted source integrals exists for any
fixed smooth periodic weight whose topological support excludes the two selected
bad configurations. Every local form-factor derivative is uniformly bounded. -/
theorem selected_complement_finite_refinement {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (theta : ℝ) (htheta : 0 < Real.sin theta)
    (hS : sourceS (Complex.exp ((theta:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ))
    (W : DoubleAngularVector (2*p) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWp : DoubleCoordinatePeriodic W)
    (hgood : ∀ u ∈ tsupport W,
      ¬ selectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) :
    ∃ (S : Finset (torusSupportBox W))
      (w : torusSupportBox W → DoubleAngularVector (2*p) → ℝ) (epsilon₀ : ℝ), 0 < epsilon₀ ∧
      (∀ c, ContDiff ℝ ∞ (w c) ∧ HasCompactSupport (w c) ∧
        (∀ u, w c u ≠ 0 → ∀ i, |u.1 i-c.1.1 i| ≤ 1/2 ∧ |u.2 i-c.1.2 i| ≤ 1/2)) ∧
      (∀ u, ∑ c ∈ S, doublePeriodicizeBump (c:DoubleAngularVector (2*p)) (w c) u = W u) ∧
      (∀ c ∈ S, ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (fun s => liftedLocalizedDoubleFormFactor (2*p)
          (sourceRadialPair theta epsilon).1 s (w c))) (sourceRadialPair theta epsilon).2‖ ≤ C) := by
  classical
  have hlocal (c : torusSupportBox W) := selected_radial_local_formFactor_bound hp hp11 ha hb
    theta htheta hS (c:DoubleAngularVector (2*p)) (hgood c c.2.1)
  choose radius eps hr he hbound using hlocal
  obtain ⟨S,w,hw,hpartition⟩ := finite_smooth_torus_refinement W hW hWp radius hr
  obtain ⟨epsilon₀,he₀,hmin⟩ := finite_positive_lower_bound S eps (fun c _ => he c)
  refine ⟨S,w,epsilon₀,he₀,?_,hpartition,?_⟩
  · intro c
    exact ⟨(hw c).1,(hw c).2.1,(hw c).2.2.2⟩
  · intro c hc j
    obtain ⟨C,hC,hb⟩ := hbound c (w c) (hw c).1 (hw c).2.2.1 j
    exact ⟨C,hC,fun epsilon hpos hsmall => hb epsilon hpos (hsmall.trans (hmin c hc))⟩

end
end IsingBulk.First
