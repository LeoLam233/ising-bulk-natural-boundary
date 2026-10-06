import IsingBulk.First.FiniteTorusBumpCover
import Mathlib.Topology.Order.Compact

/-! Exact finite refinement of an actual smooth periodic weight into compact
lifted chart pieces. Normalization is proved smooth across its zero region. -/
namespace IsingBulk.First
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff BigOperators

def torusSupportBox {N : ℕ} (W : DoubleAngularVector N → ℝ) : Set (DoubleAngularVector N) :=
  tsupport W ∩ (angleBox N ×ˢ angleBox N)

theorem torusSupportBox_compact {N : ℕ} (W : DoubleAngularVector N → ℝ) :
    IsCompact (torusSupportBox W) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    ((isClosed_tsupport W).inter (isClosed_Icc.prod isClosed_Icc))
  exact fun _ h => h.2

theorem periodic_positive_on_tsupport {N : ℕ} (W H : DoubleAngularVector N → ℝ)
    (hW : DoubleCoordinatePeriodic W) (hH : DoubleCoordinatePeriodic H) (hc : Continuous H)
    (hpos : ∀ u ∈ torusSupportBox W, 0 < H u) : ∀ u ∈ tsupport W, 0 < H u := by
  obtain ⟨m,hm,hmin⟩ := (torusSupportBox_compact W).exists_forall_le' hc.continuousOn hpos
  have hsub : Function.support W ⊆ {u | m ≤ H u} := by
    intro u hu
    let q := doubleCenteredWrap ((fun _ => Real.pi),(fun _ => Real.pi)) u
    have hqW : W q ≠ 0 := by rwa [doubleCoordinatePeriodic_wrap W hW]
    have hqK : q ∈ torusSupportBox W := ⟨subset_closure hqW,doubleCenteredWrap_pi_mem_box u⟩
    have hh := hmin q hqK
    rwa [doubleCoordinatePeriodic_wrap H hH] at hh
  have hclosed : IsClosed {u | m ≤ H u} := isClosed_le continuous_const hc
  intro u hu
  exact hm.trans_le ((closure_minimal hsub hclosed) hu)

theorem smooth_div_of_positive_on_tsupport {N : ℕ} (W H : DoubleAngularVector N → ℝ)
    (hW : ContDiff ℝ ∞ W) (hH : ContDiff ℝ ∞ H)
    (hpos : ∀ u ∈ tsupport W, 0 < H u) : ContDiff ℝ ∞ (fun u => W u/H u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport W
  · exact hW.contDiffAt.div hH.contDiffAt (hpos u hu).ne'
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hu
    have he : (fun u => W u/H u) =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [hz] with x hx
      simp only [hx,Pi.zero_apply,zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A finite source-weight partition exists with each compact lift inside its
prescribed regular-chart ball. Periodicization of the lifts sums exactly to W. -/
theorem finite_smooth_torus_refinement {N : ℕ} (W : DoubleAngularVector N → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWp : DoubleCoordinatePeriodic W)
    (radius : torusSupportBox W → ℝ) (hr : ∀ c, 0 < radius c) :
    ∃ (S : Finset (torusSupportBox W))
      (w : torusSupportBox W → DoubleAngularVector N → ℝ),
      (∀ c, ContDiff ℝ ∞ (w c) ∧ HasCompactSupport (w c) ∧
        tsupport (w c) ⊆ closedBall (c:DoubleAngularVector N) (radius c) ∧
        (∀ u, w c u ≠ 0 → ∀ i, |u.1 i-c.1.1 i| ≤ 1/2 ∧ |u.2 i-c.1.2 i| ≤ 1/2)) ∧
      (∀ u, ∑ c ∈ S, doublePeriodicizeBump (c:DoubleAngularVector N) (w c) u = W u) := by
  classical
  obtain ⟨S,b,hb,hcover⟩ := finite_torus_bump_cover (torusSupportBox_compact W) radius hr
  let H : DoubleAngularVector N → ℝ := fun u => ∑ c ∈ S, doublePeriodicizeBump (c:DoubleAngularVector N) (b c) u
  have hHs : ContDiff ℝ ∞ H := by
    apply ContDiff.sum
    intro c _
    exact doublePeriodicizeBump_contDiff _ _ (hb c).1 (hb c).2.2.2.2
  have hHp : DoubleCoordinatePeriodic H := by
    intro u i
    constructor <;> apply Finset.sum_congr rfl <;> intro c hc
    · exact (doublePeriodicizeBump_periodic _ _ u i).1
    · exact (doublePeriodicizeBump_periodic _ _ u i).2
  have hpos := periodic_positive_on_tsupport W H hWp hHp hHs.continuous hcover
  let Q : DoubleAngularVector N → ℝ := fun u => W u/H u
  have hQs : ContDiff ℝ ∞ Q := smooth_div_of_positive_on_tsupport W H hW hHs hpos
  have hQp : DoubleCoordinatePeriodic Q := by
    intro u i
    constructor
    · simp only [Q,(hWp u i).1,(hHp u i).1]
    · simp only [Q,(hWp u i).2,(hHp u i).2]
  let w : torusSupportBox W → DoubleAngularVector N → ℝ := fun c u => b c u*Q u
  refine ⟨S,w,?_,?_⟩
  · intro c
    refine ⟨(hb c).1.mul hQs,(hb c).2.1.mul_right,?_,?_⟩
    · exact tsupport_mul_subset_left.trans (hb c).2.2.2.1
    · intro u hu i
      exact (hb c).2.2.2.2 u (left_ne_zero_of_mul hu) i
  · intro u
    have he (c : torusSupportBox W) : doublePeriodicizeBump (c:DoubleAngularVector N) (w c) u =
        doublePeriodicizeBump (c:DoubleAngularVector N) (b c) u * Q u := by
      change b c (doubleCenteredWrap (c:DoubleAngularVector N) u)*Q (doubleCenteredWrap (c:DoubleAngularVector N) u) = _
      rw [doubleCoordinatePeriodic_wrap Q hQp]
      rfl
    simp_rw [he]
    rw [← Finset.sum_mul]
    change H u*(W u/H u) = W u
    by_cases hu : W u = 0
    · rw [hu,zero_div,mul_zero]
    · field_simp [(hpos u (subset_closure hu)).ne']

end
end IsingBulk.First
