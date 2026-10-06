import IsingBulk.Tail.ExteriorReducedMajorant
import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.DominatedAnalyticIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Constructed normal convergence of the actual radius-independent even
form-factor series on the upper-trace domain. No convergence certificate is
an external input. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology BigOperators

def upperTraceDomain : Set ℂ := {s | 0 < (sourceS s).im}
def upperEvenSeries (s : ℂ) : ℂ := ∑' n : ℕ, upperFormFactor (2*(n+1)) s

theorem upperTraceDomain_isOpen : IsOpen upperTraceDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hs
  apply Filter.mem_of_superset (dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm))
  intro t ht
  have hi := (one_lt_inv₀ hr).mpr hr1
  change 0 < (sourceS t).im
  have hh := ht.2
  linarith

/-- Every compact subset of the upper-trace domain admits one actual radius. -/
theorem compact_upper_common_radius {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ s ∈ K, r⁻¹-r < (sourceS s).im := by
  have hc : ContinuousOn (fun s => -(sourceS s).im) K := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro hz
      have hh := hsub hs
      simp [upperTraceDomain, sourceS, hz] at hh
    exact (Complex.continuous_im.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl).neg.continuousWithinAt
  by_cases hn : K.Nonempty
  · obtain ⟨s,hs,hmin⟩ := hK.exists_isMaxOn hn hc
    obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible (hsub hs)
    refine ⟨canonicalRadius s,hr,hr1,?_⟩
    intro t ht
    have hb := hmin ht
    change -(sourceS t).im ≤ -(sourceS s).im at hb
    linarith
  · exact ⟨1/2,by norm_num,by norm_num,fun s hs => False.elim (hn ⟨s,hs⟩)⟩

/-- A literal exponential-series majorant on every compact upper chart. -/
theorem compact_upperEven_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖upperFormFactor (2*(n+1)) s‖ ≤ u n := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_upper_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    simp [upperTraceDomain, sourceS, hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_globalRoot_inverse_bound hK hr hr1 hs0 hm
  let C₀ : ℝ := 2/(1-r^2)^2
  let B : ℝ := (r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2
  refine ⟨fun n => C₀*(B^(n+1)/(Nat.factorial (n+1):ℝ)), ?_, ?_⟩
  · exact ((Real.summable_pow_div_factorial B).comp_injective
      (fun a b h => by omega)).mul_left C₀
  · intro n s hs
    rw [upperFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
    exact even_doubleFormFactor_exponential_bound (n+1) (by omega) hr hr1 hA.le
      (hm s hs) (hi s hs)

/-- Local normal convergence is obtained from a compact closed disk, not
assumed as a physical representation input. -/
theorem upperEven_local_normal {s : ℂ} (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖upperFormFactor (2*(n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperEven_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem upperEvenSeries_analyticAt {s : ℂ} (hs : 0 < (sourceS s).im) :
    AnalyticAt ℂ upperEvenSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperEven_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (upperFormFactor_analyticAt _ (by omega) (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

/-- Every fixed differentiated actual series is normally convergent on
compact upper-trace sets. The compact constants may diverge near the boundary. -/
theorem compact_upperEven_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (upperFormFactor (2*(n+1))) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open upperTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_upperEven_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => upperFormFactor_analyticAt (2*(n+1)) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem upperEven_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (upperFormFactor (2*(n+1))) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_upperEven_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical even series, at every
fixed order and every point of its upper-trace domain. -/
theorem upperEvenSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    iteratedDeriv j upperEvenSeries s =
      ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*(n+1))) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperEven_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (upperFormFactor_analyticAt (2*(n+1)) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*(n+1))) t)
        =ᶠ[𝓝 s] iteratedDeriv j upperEvenSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem upperEven_derivative_summable (j : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (2*(n+1))) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := upperEven_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

/-- On any common fixed-radius chart the sum is the literal normalized
integral expansion; this equality involves no arbitrary continuation function. -/
theorem upperEvenSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperEvenSeries s = ∑' n : ℕ, doubleFormFactor (2*(n+1)) r s := by
  apply tsum_congr
  intro n
  exact upperFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

end
end IsingBulk.Tail
