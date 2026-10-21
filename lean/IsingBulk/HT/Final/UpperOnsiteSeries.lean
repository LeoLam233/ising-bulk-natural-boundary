import IsingBulk.HT.Final.UpperOnsiteMajorant
import IsingBulk.HT.Final.UpperOnsiteRadius
import IsingBulk.Tail.UpperExteriorSeries

/-! Constructed normal convergence and all-order differentiation of the actual odd onsite series, including N=1. These are compact-interior estimates, not the boundary-uniform HT tail estimate. -/

namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

def upperOnsiteOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, upperOnsiteFormFactor (2*n+1) s

/-- A literal exponential-series majorant on every compact upper chart. -/
theorem compact_upperOnsiteOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖upperOnsiteFormFactor (2*n+1) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_upper_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    simp [upperTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_globalRoot_inverse_bound hK hr hr1 hs0 hm
  let D : ℝ := max 1 (2*r/(1-r^2))
  let X : ℝ := r*(A*r⁻¹)*(2*r^2/(1-r^2))
  let C₀ : ℝ := X*D
  let B : ℝ := X^2*D/2
  refine ⟨fun n => C₀*(B^n/(Nat.factorial n:ℝ)), ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial B).mul_left C₀
  · intro n s hs
    rw [upperOnsiteFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact odd_onsiteFormFactor_exponential_bound n hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem upperOnsiteOdd_local_normal {s : ℂ} (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖upperOnsiteFormFactor (2*n+1) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperOnsiteOdd_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem upperOnsiteOddSeries_analyticAt {s : ℂ} (hs : 0 < (sourceS s).im) :
    AnalyticAt ℂ upperOnsiteOddSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperOnsiteOdd_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (upperOnsiteFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact upper-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_upperOnsiteOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open upperTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_upperOnsiteOdd_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => upperOnsiteFormFactor_analyticAt (2*n+1) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem upperOnsiteOdd_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperOnsiteOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical odd series, at every
fixed order and every point of its upper-trace domain. -/
theorem upperOnsiteOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    iteratedDeriv j upperOnsiteOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperOnsiteOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (upperOnsiteFormFactor_analyticAt (2*n+1) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) t)
        =ᶠ[𝓝 s] iteratedDeriv j upperOnsiteOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem upperOnsiteOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := upperOnsiteOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem upperOnsiteOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperOnsiteOddSeries s = ∑' n : ℕ, onsiteFormFactor (2*n+1) r s := by
  apply tsum_congr
  intro n
  exact upperOnsiteFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

end
end IsingBulk.HT.Final
