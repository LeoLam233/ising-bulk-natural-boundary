import IsingBulk.Tail.RightReducedMajorant
import IsingBulk.Tail.RightFormFactorAnalytic
import IsingBulk.First.DominatedAnalyticIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Constructed normal convergence of the actual radius-independent even
form-factor series on the right-trace domain. No convergence certificate is
an external input. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology BigOperators

def rightTraceDomain : Set ℂ := {s | 2 < (sourceS s).re}
def rightEvenSeries (s : ℂ) : ℂ := ∑' n : ℕ, rightFormFactor (2*(n+1)) s

theorem rightTraceDomain_isOpen : IsOpen rightTraceDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hs0 : s ≠ 0 := by
    intro hz
    norm_num [rightTraceDomain, sourceS, hz] at hs
  have hc : ContinuousAt (fun t : ℂ => (sourceS t).re) s :=
    Complex.continuous_re.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl
  exact hc.eventually (Ioi_mem_nhds hs)

/-- Every compact subset of the right-trace domain admits one actual radius. -/
theorem compact_right_common_radius {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ s ∈ K, 1+r⁻¹ < (sourceS s).re := by
  have hc : ContinuousOn (fun s => -(sourceS s).re) K := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro hz
      have hh := hsub hs
      norm_num [rightTraceDomain, sourceS, hz] at hh
    exact (Complex.continuous_re.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl).neg.continuousWithinAt
  by_cases hn : K.Nonempty
  · obtain ⟨s,hs,hmin⟩ := hK.exists_isMaxOn hn hc
    obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible (hsub hs)
    refine ⟨rightCanonicalRadius s,hr,hr1,?_⟩
    intro t ht
    have hb := hmin ht
    change -(sourceS t).re ≤ -(sourceS s).re at hb
    linarith
  · exact ⟨1/2,by norm_num,by norm_num,fun s hs => False.elim (hn ⟨s,hs⟩)⟩

/-- A literal exponential-series majorant on every compact right chart. -/
theorem compact_rightEven_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖rightFormFactor (2*(n+1)) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_right_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    norm_num [rightTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_rightRoot_inverse_bound hK hr hr1 hs0 hm
  let C₀ : ℝ := 2/(1-r^2)^2
  let B : ℝ := (r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2
  refine ⟨fun n => C₀*(B^(n+1)/(Nat.factorial (n+1):ℝ)), ?_, ?_⟩
  · exact ((Real.summable_pow_div_factorial B).comp_injective
      (fun a b h => by omega)).mul_left C₀
  · intro n s hs
    rw [rightFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact right_even_doubleFormFactor_exponential_bound (n+1) (by omega) hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem rightEven_local_normal {s : ℂ} (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖rightFormFactor (2*(n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (rightTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ rightTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_rightEven_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem rightEvenSeries_analyticAt {s : ℂ} (hs : 2 < (sourceS s).re) :
    AnalyticAt ℂ rightEvenSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := rightEven_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (rightFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact right-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_rightEven_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (rightFormFactor (2*(n+1))) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open rightTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_rightEven_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => rightFormFactor_analyticAt (2*(n+1)) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem rightEven_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (rightFormFactor (2*(n+1))) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (rightTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ rightTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_rightEven_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical even series, at every
fixed order and every point of its right-trace domain. -/
theorem rightEvenSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    iteratedDeriv j rightEvenSeries s =
      ∑' n : ℕ, iteratedDeriv j (rightFormFactor (2*(n+1))) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := rightEven_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (rightFormFactor_analyticAt (2*(n+1)) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (rightFormFactor (2*(n+1))) t)
        =ᶠ[𝓝 s] iteratedDeriv j rightEvenSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem rightEven_derivative_summable (j : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (rightFormFactor (2*(n+1))) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := rightEven_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem rightEvenSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightEvenSeries s = ∑' n : ℕ, doubleFormFactor (2*(n+1)) r s := by
  apply tsum_congr
  intro n
  exact rightFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

end
end IsingBulk.Tail
