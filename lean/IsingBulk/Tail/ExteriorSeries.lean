import IsingBulk.Tail.ExteriorFormFactors
import IsingBulk.First.NearInfinityBulkSeries

/-! Whole-exterior normal convergence and termwise derivatives of the actual
glued source series. Compact majorants are constructed from finitely many
actual contour charts, rather than imported as E1. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology BigOperators

def exteriorEvenSeries (s : ℂ) : ℂ := ∑' n : ℕ, exteriorEvenTerm n s

theorem exteriorEven_local_majorant_raw {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ U → ‖exteriorEvenTerm n t‖ ≤ u n := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := upperEven_local_normal hu
    refine ⟨U,hU,hsU,u,hsum,?_⟩
    intro n t ht
    rw [exteriorEvenTerm_eq_upper n (hsub ht)]
    exact hb n t ht
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := upperEven_local_normal hc
    refine ⟨(fun t : ℂ => star t) ⁻¹' U,hU.preimage continuous_star,hsU,u,hsum,?_⟩
    intro n t ht
    have hlt : (sourceS t).im < 0 := by
      have hh := hsub ht
      simpa [upperTraceDomain] using hh
    rw [exteriorEvenTerm_eq_lower n hlt,norm_star]
    exact hb n (star t) ht
  · obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := rightEven_local_normal hr
    refine ⟨U,hU,hsU,u,hsum,?_⟩
    intro n t ht
    rw [exteriorEvenTerm_eq_right n (hsub ht)]
    exact hb n t ht
  · have hn : 2 < (sourceS (-s)).re := by simp only [sourceS_neg,Complex.neg_re]; linarith
    obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := rightEven_local_normal hn
    refine ⟨(fun t : ℂ => -t) ⁻¹' U,hU.preimage continuous_neg,hsU,u,hsum,?_⟩
    intro n t ht
    have hlt : (sourceS t).re < -2 := by
      have hh := hsub ht
      change 2 < (sourceS (-t)).re at hh
      rw [sourceS_neg,Complex.neg_re] at hh
      linarith
    rw [exteriorEvenTerm_eq_left n hlt]
    exact hb n (-t) ht

theorem exteriorEven_local_normal {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ exteriorDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U → ‖exteriorEvenTerm n t‖ ≤ u n := by
  obtain ⟨U,hU,hsU,u,hu,hb⟩ := exteriorEven_local_majorant_raw hs
  exact ⟨U ∩ exteriorDomain,hU.inter exteriorDomain_isOpen,⟨hsU,hs⟩,
    inter_subset_right,u,hu,fun n t ht => hb n t ht.1⟩

/-- Every compact exterior set has a summable majorant for the actual series.
The finite-cover argument does not request a common radius for the whole exterior. -/
theorem compact_exteriorEven_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖exteriorEvenTerm n s‖ ≤ u n := by
  apply hK.induction_on (p := fun L => ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n s, s ∈ L → ‖exteriorEvenTerm n s‖ ≤ u n)
  · exact ⟨0,summable_zero,by simp⟩
  · intro L M hLM hM
    obtain ⟨u,hu,hb⟩ := hM
    exact ⟨u,hu,fun n s hs => hb n s (hLM hs)⟩
  · intro L M hL hM
    obtain ⟨u,hu,hbu⟩ := hL
    obtain ⟨v,hv,hbv⟩ := hM
    refine ⟨fun n => ‖u n‖+‖v n‖,hu.norm.add hv.norm,?_⟩
    intro n s hs
    rcases hs with hs | hs
    · exact (hbu n s hs).trans ((show u n ≤ ‖u n‖ by simpa only [Real.norm_eq_abs] using le_abs_self (u n)).trans (le_add_of_nonneg_right (norm_nonneg _)))
    · exact (hbv n s hs).trans ((show v n ≤ ‖v n‖ by simpa only [Real.norm_eq_abs] using le_abs_self (v n)).trans (le_add_of_nonneg_left (norm_nonneg _)))
  · intro s hs
    obtain ⟨U,hU,hsU,_hsub,u,hu,hb⟩ := exteriorEven_local_normal (hsub hs)
    exact ⟨U,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hsU),u,hu,hb⟩

theorem exteriorEvenSeries_analyticAt {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ exteriorEvenSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := exteriorEven_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (exteriorEvenTerm_analyticAt n (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

theorem compact_exteriorEven_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (exteriorEvenTerm n) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open exteriorDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_exteriorEven_majorant hK.cthickening hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n,hu.mul_left _,?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => exteriorEvenTerm_analyticAt n (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem exteriorEven_derivative_local_normal (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ exteriorDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (exteriorEvenTerm n) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (exteriorDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ exteriorDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_exteriorEven_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  exact ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,fun n t ht => hb n t (ball_subset_closedBall ht)⟩

theorem exteriorEvenSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    iteratedDeriv j exteriorEvenSeries s = ∑' n : ℕ, iteratedDeriv j (exteriorEvenTerm n) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := exteriorEven_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (exteriorEvenTerm_analyticAt n (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (exteriorEvenTerm n) t)
        =ᶠ[𝓝 s] iteratedDeriv j exteriorEvenSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

theorem exteriorEven_derivative_summable (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (exteriorEvenTerm n) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := exteriorEven_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

theorem exteriorEvenSeries_eq_upper {s : ℂ} (hs : 0 < (sourceS s).im) :
    exteriorEvenSeries s = upperEvenSeries s :=
  tsum_congr (fun n => exteriorEvenTerm_eq_upper n hs)

def exteriorNormalizedBulk (s : ℂ) : ℂ :=
  1-magnetizationSquared s+2*magnetizationSquared s*exteriorEvenSeries s

theorem exteriorNormalizedBulk_analyticOn : AnalyticOnNhd ℂ exteriorNormalizedBulk exteriorDomain := by
  intro s hs
  exact ((analyticAt_const.sub (magnetizationSquared_analyticOn_exterior s hs))).add
    (((analyticAt_const.mul (magnetizationSquared_analyticOn_exterior s hs))).mul
      (exteriorEvenSeries_analyticAt hs))

/-- Identification with the exact FIRST normalized germ near infinity. -/
theorem exteriorNormalizedBulk_eq_quarter_far {s : ℂ} (hs : 16 < ‖s‖) :
    exteriorNormalizedBulk s = normalizedBulkSeries (1/4) s := by
  have he : exteriorEvenSeries s = ∑' n : ℕ, doubleFormFactor (2*(n+1)) (1/4) s :=
    tsum_congr (fun n => exteriorEvenTerm_eq_quarter_far n hs)
  simp only [exteriorNormalizedBulk,normalizedBulkSeries,he]

end
end IsingBulk.Tail
