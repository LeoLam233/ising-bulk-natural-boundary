import IsingBulk.HT.Tail.OddExteriorMajorant
import IsingBulk.Tail.UpperExteriorSeries

/-!
# Normal convergence of the complete upper-trace odd offsite series

The compact geometry, fixed-radius analytic lemmas, Cauchy estimate and
termwise-differentiation theorem are reused from LT.  The source majorant
is the newly proved odd factorial bound; no even-series convergence is
substituted for the odd assertion.  The positive upper-trace chart is
explicit.  This file does not claim the signed reflection/gluing or the
full-site onsite estimate.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

def upperOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, upperFormFactor (2*n+1) s

/-- A literal exponential-series majorant on every compact upper chart. -/
theorem compact_upperOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖upperFormFactor (2*n+1) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_upper_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    simp [upperTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_globalRoot_inverse_bound hK hr hr1 hs0 hm
  let D : ℝ := max 1 (2*r/(1-r^2))
  let X : ℝ := r*(max A r⁻¹)*(2*r^2/(1-r^2))
  let C₀ : ℝ := 2*X*D/(1-r)^2
  let B : ℝ := X^2*D/2
  refine ⟨fun n => C₀*(B^n/(Nat.factorial n:ℝ)), ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial B).mul_left C₀
  · intro n s hs
    rw [upperFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact odd_doubleFormFactor_exponential_bound n hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem upperOdd_local_normal {s : ℂ} (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖upperFormFactor (2*n+1) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperOdd_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem upperOddSeries_analyticAt {s : ℂ} (hs : 0 < (sourceS s).im) :
    AnalyticAt ℂ upperOddSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperOdd_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (upperFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact upper-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_upperOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (upperFormFactor (2*n+1)) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open upperTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_upperOdd_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => upperFormFactor_analyticAt (2*n+1) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem upperOdd_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (upperFormFactor (2*n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical odd series, at every
fixed order and every point of its upper-trace domain. -/
theorem upperOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    iteratedDeriv j upperOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*n+1)) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (upperFormFactor_analyticAt (2*n+1) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*n+1)) t)
        =ᶠ[𝓝 s] iteratedDeriv j upperOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem upperOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (2*n+1)) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := upperOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem upperOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperOddSeries s = ∑' n : ℕ, doubleFormFactor (2*n+1) r s := by
  apply tsum_congr
  intro n
  exact upperFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

end
end IsingBulk.HT.Tail
