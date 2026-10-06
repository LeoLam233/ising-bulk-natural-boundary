import IsingBulk.First.FiniteTorusRefinement
import IsingBulk.First.OnsiteLocalFormFactor

/-! The onsite source has no bad angular configurations. A genuine finite
smooth periodic partition of the constant weight one is constructed. -/
namespace IsingBulk.First
noncomputable section
open Set Metric
open scoped Topology ContDiff BigOperators

private theorem onsite_finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
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

theorem onsite_finite_refinement {N : ℕ} (hN : 0 < N)
    (level : ℝ) (hlevel : 0 < level ∧ level < 2)
    (theta : ℝ) (htheta : 0 < Real.sin theta)
    (hS : sourceS (Complex.exp ((theta:ℂ)*Complex.I)) = (level:ℂ)) :
    ∃ (S : Finset (torusSupportBox (fun _ : DoubleAngularVector N => (1:ℝ))))
      (w : torusSupportBox (fun _ : DoubleAngularVector N => (1:ℝ)) → DoubleAngularVector N → ℝ)
      (epsilon₀ : ℝ), 0 < epsilon₀ ∧
      (∀ c, ContDiff ℝ ∞ (w c) ∧ HasCompactSupport (w c) ∧
        (∀ u, w c u ≠ 0 → ∀ i, |u.1 i-c.1.1 i| ≤ 1/2 ∧ |u.2 i-c.1.2 i| ≤ 1/2)) ∧
      (∀ u, ∑ c ∈ S, doublePeriodicizeBump (c:DoubleAngularVector N) (w c) u = 1) ∧
      (∀ c ∈ S, ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (fun s => liftedLocalizedOnsiteFormFactor N
          (sourceRadialPair theta epsilon).1 s (w c))) (sourceRadialPair theta epsilon).2‖ ≤ C) := by
  classical
  let W : DoubleAngularVector N → ℝ := fun _ => 1
  have hlocal (c : torusSupportBox W) := onsite_radial_local_formFactor_bound hN level hlevel
    theta htheta hS (c:DoubleAngularVector N)
  choose radius eps hr he hbound using hlocal
  have hWp : DoubleCoordinatePeriodic W := by intro u i; exact ⟨rfl,rfl⟩
  obtain ⟨S,w,hw,hpartition⟩ := finite_smooth_torus_refinement W contDiff_const hWp radius hr
  obtain ⟨epsilon₀,he₀,hmin⟩ := onsite_finite_positive_lower_bound S eps (fun c _ => he c)
  refine ⟨S,w,epsilon₀,he₀,?_,hpartition,?_⟩
  · intro c
    exact ⟨(hw c).1,(hw c).2.1,(hw c).2.2.2⟩
  · intro c hc j
    obtain ⟨C,hC,hb⟩ := hbound c (w c) (hw c).1 (hw c).2.2.1 j
    exact ⟨C,hC,fun epsilon hpos hsmall => hb epsilon hpos (hsmall.trans (hmin c hc))⟩

end
end IsingBulk.First
