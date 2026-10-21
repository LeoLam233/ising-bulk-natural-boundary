import IsingBulk.HT.Tail.RightOddMajorant
import IsingBulk.HT.Tail.UpperOddSeries
import IsingBulk.Tail.RightExteriorSeries

/-!
# Complete right-trace odd offsite series

The actual one-Pfaffian odd factorial majorant proves normal convergence
on compact right-trace sets, including charts across the positive real
exterior axis. All fixed derivative orders commute with the literal full
odd sum. Only established all-N radius, analytic and Cauchy infrastructure
is reused; no even-series convergence is substituted for an odd claim.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

def rightOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, rightFormFactor (2*n+1) s

/-- A literal exponential-series majorant on every compact right chart. -/
theorem compact_rightOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖rightFormFactor (2*n+1) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_right_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    norm_num [rightTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_rightRoot_inverse_bound hK hr hr1 hs0 hm
  let D : ℝ := max 1 (2*r/(1-r^2))
  let X : ℝ := r*(max A r⁻¹)*(2*r^2/(1-r^2))
  let C₀ : ℝ := 2*X*D/(1-r)^2
  let B : ℝ := X^2*D/2
  refine ⟨fun n => C₀*(B^n/(Nat.factorial n:ℝ)), ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial B).mul_left C₀
  · intro n s hs
    rw [rightFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact right_odd_doubleFormFactor_exponential_bound n hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem rightOdd_local_normal {s : ℂ} (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖rightFormFactor (2*n+1) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (rightTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ rightTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_rightOdd_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem rightOddSeries_analyticAt {s : ℂ} (hs : 2 < (sourceS s).re) :
    AnalyticAt ℂ rightOddSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := rightOdd_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (rightFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact right-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_rightOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (rightFormFactor (2*n+1)) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open rightTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_rightOdd_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => rightFormFactor_analyticAt (2*n+1) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem rightOdd_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (rightFormFactor (2*n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (rightTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ rightTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_rightOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical odd series, at every
fixed order and every point of its right-trace domain. -/
theorem rightOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    iteratedDeriv j rightOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (rightFormFactor (2*n+1)) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := rightOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (rightFormFactor_analyticAt (2*n+1) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (rightFormFactor (2*n+1)) t)
        =ᶠ[𝓝 s] iteratedDeriv j rightOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem rightOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (rightFormFactor (2*n+1)) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := rightOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem rightOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightOddSeries s = ∑' n : ℕ, doubleFormFactor (2*n+1) r s := by
  apply tsum_congr
  intro n
  exact rightFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

/-- The odd series glue on their actual overlap by all-N radius
independence, without an assumed analytic continuation function. -/
theorem rightOddSeries_eq_upper {s : ℂ}
    (hs : 2 < (sourceS s).re) (hu : 0 < (sourceS s).im) :
    rightOddSeries s = upperOddSeries s := by
  apply tsum_congr
  intro n
  exact rightFormFactor_eq_upper _ (by omega) hs hu

/-- The gluing is an open-neighborhood identity, hence survives every
fixed complex derivative. -/
theorem rightOddSeries_iteratedDeriv_eq_upper (j : ℕ) {s : ℂ}
    (hs : 2 < (sourceS s).re) (hu : 0 < (sourceS s).im) :
    iteratedDeriv j rightOddSeries s = iteratedDeriv j upperOddSeries s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [rightTraceDomain_isOpen.mem_nhds hs,
    upperTraceDomain_isOpen.mem_nhds hu] with t ht htU
  exact rightOddSeries_eq_upper ht htU

end
end IsingBulk.HT.Tail
