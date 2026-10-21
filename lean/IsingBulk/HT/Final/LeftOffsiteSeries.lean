import IsingBulk.HT.Final.LeftOffsiteMajorant
import IsingBulk.HT.Final.LeftOffsiteAnalytic
import IsingBulk.HT.Tail.UpperOddSeries
import IsingBulk.Tail.ExteriorFormFactors

/-!
# Complete left-trace odd offsite series

The actual one-Pfaffian odd factorial majorant proves normal convergence
on compact left-trace sets, including charts across the negative real
exterior axis. All fixed derivative orders commute with the literal full
odd sum. Only established all-N radius, analytic and Cauchy infrastructure
is reused; no even-series convergence is substituted for an odd claim.
-/

namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set Filter Metric
open scoped Topology BigOperators


/-- Reflection is used only to choose an admissible radius; the form factor
itself remains the original unsigned double contour at s. -/
theorem compact_left_common_radius {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ leftTraceDomain) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ s ∈ K, 1+r⁻¹ < -(sourceS s).re := by
  have him : (fun s : ℂ => -s) '' K ⊆ rightTraceDomain := by
    rintro t ⟨s,hs,rfl⟩
    have hh := hsub hs
    change (sourceS s).re < -2 at hh
    change 2 < (sourceS (-s)).re
    simp only [sourceS_neg,Complex.neg_re]
    linarith
  obtain ⟨r,hr,hr1,hb⟩ := compact_right_common_radius (hK.image continuous_neg) him
  refine ⟨r,hr,hr1,?_⟩
  intro s hs
  simpa only [sourceS_neg,Complex.neg_re] using hb (-s) ⟨s,hs,rfl⟩

def leftOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, leftFormFactor (2*n+1) s

/-- A literal exponential-series majorant on every compact left chart. -/
theorem compact_leftOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ leftTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖leftFormFactor (2*n+1) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_left_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    norm_num [leftTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_leftRoot_inverse_bound hK hr hr1 hs0 hm
  let D : ℝ := max 1 (2*r/(1-r^2))
  let X : ℝ := r*(max A r⁻¹)*(2*r^2/(1-r^2))
  let C₀ : ℝ := 2*X*D/(1-r)^2
  let B : ℝ := X^2*D/2
  refine ⟨fun n => C₀*(B^n/(Nat.factorial n:ℝ)), ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial B).mul_left C₀
  · intro n s hs
    rw [leftFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact left_odd_doubleFormFactor_exponential_bound n hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem leftOdd_local_normal {s : ℂ} (hs : (sourceS s).re < -2) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ leftTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖leftFormFactor (2*n+1) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (leftTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ leftTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_leftOdd_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem leftOddSeries_analyticAt {s : ℂ} (hs : (sourceS s).re < -2) :
    AnalyticAt ℂ leftOddSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := leftOdd_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (leftFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact left-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_leftOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ leftTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (leftFormFactor (2*n+1)) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open leftTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_leftOdd_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => leftFormFactor_analyticAt (2*n+1) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem leftOdd_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : (sourceS s).re < -2) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ leftTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (leftFormFactor (2*n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (leftTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ leftTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_leftOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical odd series, at every
fixed order and every point of its left-trace domain. -/
theorem leftOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    iteratedDeriv j leftOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (leftFormFactor (2*n+1)) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := leftOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (leftFormFactor_analyticAt (2*n+1) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (leftFormFactor (2*n+1)) t)
        =ᶠ[𝓝 s] iteratedDeriv j leftOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem leftOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (leftFormFactor (2*n+1)) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := leftOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem leftOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftOddSeries s = ∑' n : ℕ, doubleFormFactor (2*n+1) r s := by
  apply tsum_congr
  intro n
  exact leftFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

/-- The odd series glue on their actual overlap by all-N radius
independence, without an assumed analytic continuation function. -/
theorem leftOddSeries_eq_upper {s : ℂ}
    (hs : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    leftOddSeries s = upperOddSeries s := by
  apply tsum_congr
  intro n
  exact leftFormFactor_eq_upper _ (by omega) hs hu

/-- The gluing is an open-neighborhood identity, hence survives every
fixed complex derivative. -/
theorem leftOddSeries_iteratedDeriv_eq_upper (j : ℕ) {s : ℂ}
    (hs : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    iteratedDeriv j leftOddSeries s = iteratedDeriv j upperOddSeries s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [leftTraceDomain_isOpen.mem_nhds hs,
    upperTraceDomain_isOpen.mem_nhds hu] with t ht htU
  exact leftOddSeries_eq_upper ht htU

end
end IsingBulk.HT.Final
