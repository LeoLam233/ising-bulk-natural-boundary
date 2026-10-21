import IsingBulk.HT.Final.ExteriorFullTerms

/-! Whole-exterior normal convergence and termwise derivatives of the actual
glued source series. Compact majorants are constructed from finitely many
actual contour charts, rather than imported as E1. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

def exteriorOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, exteriorOddTerm n s

theorem exteriorOdd_local_majorant_raw {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ U → ‖exteriorOddTerm n t‖ ≤ u n := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := upperFull_local_normal hu
    refine ⟨U,hU,hsU,u,hsum,?_⟩
    intro n t ht
    rw [exteriorOddTerm_eq_upper n (hsub ht)]
    exact hb n t ht
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := upperFull_local_normal hc
    refine ⟨(fun t : ℂ => star t) ⁻¹' U,hU.preimage continuous_star,hsU,u,hsum,?_⟩
    intro n t ht
    have hlt : (sourceS t).im < 0 := by
      have hh := hsub ht
      simpa [upperTraceDomain] using hh
    rw [exteriorOddTerm_eq_lower n hlt,norm_star]
    exact hb n (star t) ht
  · obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := rightFull_local_normal hr
    refine ⟨U,hU,hsU,u,hsum,?_⟩
    intro n t ht
    rw [exteriorOddTerm_eq_right n (hsub ht)]
    exact hb n t ht
  · obtain ⟨U,hU,hsU,hsub,u,hsum,hb⟩ := leftFull_local_normal hL
    refine ⟨U,hU,hsU,u,hsum,?_⟩
    intro n t ht
    rw [exteriorOddTerm_eq_left n (hsub ht)]
    exact hb n t ht

theorem exteriorOdd_local_normal {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ exteriorDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U → ‖exteriorOddTerm n t‖ ≤ u n := by
  obtain ⟨U,hU,hsU,u,hu,hb⟩ := exteriorOdd_local_majorant_raw hs
  exact ⟨U ∩ exteriorDomain,hU.inter exteriorDomain_isOpen,⟨hsU,hs⟩,
    inter_subset_right,u,hu,fun n t ht => hb n t ht.1⟩

/-- Every compact exterior set has a summable majorant for the actual series.
The finite-cover argument does not request a common radius for the whole exterior. -/
theorem compact_exteriorOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K → ‖exteriorOddTerm n s‖ ≤ u n := by
  apply hK.induction_on (p := fun L => ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n s, s ∈ L → ‖exteriorOddTerm n s‖ ≤ u n)
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
    obtain ⟨U,hU,hsU,_hsub,u,hu,hb⟩ := exteriorOdd_local_normal (hsub hs)
    exact ⟨U,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hsU),u,hu,hb⟩

theorem exteriorOddSeries_analyticAt {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ exteriorOddSeries s := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := exteriorOdd_local_normal hs
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hsU)
  exact Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n t ht => (exteriorOddTerm_analyticAt n (hsub ht)).differentiableAt.differentiableWithinAt)
    hU hb

theorem compact_exteriorOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (exteriorOddTerm n) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open exteriorDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_exteriorOdd_majorant hK.cthickening hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n,hu.mul_left _,?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => exteriorOddTerm_analyticAt n (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem exteriorOdd_derivative_local_normal (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ exteriorDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (exteriorOddTerm n) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (exteriorDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ exteriorDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_exteriorOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  exact ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,fun n t ht => hb n t (ball_subset_closedBall ht)⟩

theorem exteriorOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    iteratedDeriv j exteriorOddSeries s = ∑' n : ℕ, iteratedDeriv j (exteriorOddTerm n) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := exteriorOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (exteriorOddTerm_analyticAt n (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (exteriorOddTerm n) t)
        =ᶠ[𝓝 s] iteratedDeriv j exteriorOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

theorem exteriorOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (exteriorOddTerm n) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := exteriorOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)

theorem exteriorOddSeries_eq_upper {s : ℂ} (hs : 0 < (sourceS s).im) :
    exteriorOddSeries s = upperFullOddSeries s :=
  tsum_congr (fun n => exteriorOddTerm_eq_upper n hs)


/-- The actual full odd bulk series, with the HT prefactor. -/
def exteriorFullBulk (s : ℂ) : ℂ := exteriorPrefactor s*exteriorOddSeries s

theorem exteriorFullBulk_analyticOn : AnalyticOnNhd ℂ exteriorFullBulk exteriorDomain := by
  intro s hs
  exact (exteriorPrefactor_analyticOn s hs).mul (exteriorOddSeries_analyticAt hs)

theorem exteriorOddSeries_eq_quarter_far {s : ℂ} (hs : 16 < ‖s‖) :
    exteriorOddSeries s = fixedOddFullSeries (1/4) s :=
  tsum_congr (fun n => exteriorOddTerm_eq_quarter_far n hs)

theorem exteriorFullBulk_eq_quarter_far {s : ℂ} (hs : 16 < ‖s‖) :
    exteriorFullBulk s = fixedNormalizedBulk (1/4) s := by
  simp only [exteriorFullBulk,fixedNormalizedBulk,exteriorOddSeries_eq_quarter_far hs]

theorem exteriorOddSeries_conjugate {s : ℂ} (hs : 1 < ‖s‖) :
    exteriorOddSeries (star s) = star (exteriorOddSeries s) := by
  simp only [exteriorOddSeries,exteriorOddTerm_conjugate _ hs,tsum_star]

/-- The full infinite derivative series is identified with the genuine
upper source construction on an open neighborhood, before boundary limits. -/
theorem exteriorOddSeries_iteratedDeriv_eq_upper (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    iteratedDeriv j exteriorOddSeries s = iteratedDeriv j upperFullOddSeries s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [upperTraceDomain_isOpen.mem_nhds hs] with t ht
  exact exteriorOddSeries_eq_upper ht

end
end IsingBulk.HT.Final
