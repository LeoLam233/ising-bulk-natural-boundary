import IsingBulk.Tail.ExteriorSeries

/-! Explicit Appendix C root-test scale. The one-Pfaffian proof gives the
stronger exponential-series bound; this module recovers the displayed
C₀(C/√N)^N estimate and its compact Cauchy derivative majorants. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology BigOperators

theorem factorial_majorant_le_sqrt (m : ℕ) (hm : 0 < m) {B : ℝ} (hB : 0 ≤ B) :
    B^m/(m.factorial:ℝ) ≤ ((2*(Real.exp 1*B+1))/Real.sqrt (2*m))^(2*m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hfac := factorial_lower_exp m
  have hb : B^m/(m.factorial:ℝ) ≤ (Real.exp 1*B/(m:ℝ))^m := by
    calc
      _ ≤ B^m/(((m:ℝ)/Real.exp 1)^m) :=
        div_le_div₀ (pow_nonneg hB _) le_rfl (pow_pos (div_pos hm0 he) _) hfac
      _ = _ := by rw [← div_pow]; congr 1; field_simp
  have hbase : Real.exp 1*B/(m:ℝ) ≤ (2*(Real.exp 1*B+1))^2/(2*m) := by
    apply (div_le_div_iff₀ hm0 (by positivity : (0:ℝ)<2*m)).mpr
    have hp : 0 ≤ Real.exp 1*B := mul_nonneg he.le hB
    nlinarith [sq_nonneg (Real.exp 1*B),mul_nonneg hm0.le (sq_nonneg (Real.exp 1*B)),
      mul_nonneg hm0.le hp]
  apply hb.trans
  have hpow := pow_le_pow_left₀ (div_nonneg (mul_nonneg he.le hB) hm0.le) hbase m
  have hroot : (Real.sqrt (2*(m:ℝ)))^2 = 2*m := Real.sq_sqrt (by positivity)
  calc
    _ ≤ ((2*(Real.exp 1*B+1))^2/(2*m))^m := hpow
    _ = _ := by simp only [pow_mul,div_pow,hroot]

theorem compact_upperEven_exponential_constants {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ upperTraceDomain) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ n s, s ∈ K →
      ‖upperFormFactor (2*(n+1)) s‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_upper_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    simp [upperTraceDomain,sourceS,hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_globalRoot_inverse_bound hK hr hr1 hs0 hm
  have hg : 0 < 1-r^2 := by nlinarith
  refine ⟨2/(1-r^2)^2,(r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2,
    by positivity,by positivity,?_⟩
  intro n s hs
  rw [upperFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
  exact even_doubleFormFactor_exponential_bound (n+1) (by omega) hr hr1 hA.le
    (hm s hs) (hi s hs)

theorem compact_rightEven_exponential_constants {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ rightTraceDomain) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ n s, s ∈ K →
      ‖rightFormFactor (2*(n+1)) s‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  obtain ⟨r,hr,hr1,hm⟩ := compact_right_common_radius hK hsub
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs hz
    have hh := hsub hs
    norm_num [rightTraceDomain,sourceS,hz] at hh
  obtain ⟨A,hA,hi⟩ := compact_rightRoot_inverse_bound hK hr hr1 hs0 hm
  have hg : 0 < 1-r^2 := by nlinarith
  refine ⟨2/(1-r^2)^2,(r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2,
    by positivity,by positivity,?_⟩
  intro n s hs
  rw [rightFormFactor_eq_fixed_radius _ (by omega) hr hr1 (hm s hs)]
  exact right_even_doubleFormFactor_exponential_bound (n+1) (by omega) hr hr1 hA.le
    (hm s hs) (hi s hs)

theorem upperEven_local_exponential_constants {s : ℂ} (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ n t, t ∈ U →
        ‖upperFormFactor (2*(n+1)) t‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (upperTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ upperTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C₀,B,hC,hB,hb⟩ := compact_upperEven_exponential_constants (isCompact_closedBall s (ε/2)) hK
  exact ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,C₀,B,hC,hB,fun n t ht => hb n t (ball_subset_closedBall ht)⟩

theorem rightEven_local_exponential_constants {s : ℂ} (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ n t, t ∈ U →
        ‖rightFormFactor (2*(n+1)) t‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (rightTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ rightTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C₀,B,hC,hB,hb⟩ := compact_rightEven_exponential_constants (isCompact_closedBall s (ε/2)) hK
  exact ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,C₀,B,hC,hB,fun n t ht => hb n t (ball_subset_closedBall ht)⟩

theorem exteriorEven_local_exponential_constants {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧
      ∀ n t, t ∈ U → ‖exteriorEvenTerm n t‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · obtain ⟨U,hU,hsU,hsub,C₀,B,hC,hB,hb⟩ := upperEven_local_exponential_constants hu
    refine ⟨U,hU,hsU,C₀,B,hC,hB,?_⟩
    intro n t ht
    rw [exteriorEvenTerm_eq_upper n (hsub ht)]
    exact hb n t ht
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    obtain ⟨U,hU,hsU,hsub,C₀,B,hC,hB,hb⟩ := upperEven_local_exponential_constants hc
    refine ⟨(fun t : ℂ => star t) ⁻¹' U,hU.preimage continuous_star,hsU,C₀,B,hC,hB,?_⟩
    intro n t ht
    have hlt : (sourceS t).im < 0 := by
      have hh := hsub ht
      simpa [upperTraceDomain] using hh
    rw [exteriorEvenTerm_eq_lower n hlt,norm_star]
    exact hb n (star t) ht
  · obtain ⟨U,hU,hsU,hsub,C₀,B,hC,hB,hb⟩ := rightEven_local_exponential_constants hr
    refine ⟨U,hU,hsU,C₀,B,hC,hB,?_⟩
    intro n t ht
    rw [exteriorEvenTerm_eq_right n (hsub ht)]
    exact hb n t ht
  · have hn : 2 < (sourceS (-s)).re := by simp only [sourceS_neg,Complex.neg_re]; linarith
    obtain ⟨U,hU,hsU,hsub,C₀,B,hC,hB,hb⟩ := rightEven_local_exponential_constants hn
    refine ⟨(fun t : ℂ => -t) ⁻¹' U,hU.preimage continuous_neg,hsU,C₀,B,hC,hB,?_⟩
    intro n t ht
    have hlt : (sourceS t).re < -2 := by
      have hh := hsub ht
      change 2 < (sourceS (-t)).re at hh
      rw [sourceS_neg,Complex.neg_re] at hh
      linarith
    rw [exteriorEvenTerm_eq_left n hlt]
    exact hb n (-t) ht

theorem compact_exteriorEven_exponential_constants {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ n s, s ∈ K →
      ‖exteriorEvenTerm n s‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)) := by
  apply hK.induction_on (p := fun L => ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧
      ∀ n s, s ∈ L → ‖exteriorEvenTerm n s‖ ≤ C₀*(B^(n+1)/((n+1).factorial:ℝ)))
  · exact ⟨0,0,le_rfl,le_rfl,by simp⟩
  · intro L M hLM hM
    obtain ⟨C₀,B,hC,hB,hb⟩ := hM
    exact ⟨C₀,B,hC,hB,fun n s hs => hb n s (hLM hs)⟩
  · intro L M hL hM
    obtain ⟨C₀,B,hC,hB,hb⟩ := hL
    obtain ⟨D₀,E,hD,hE,he⟩ := hM
    refine ⟨C₀+D₀,max B E,add_nonneg hC hD,hB.trans (le_max_left _ _),?_⟩
    intro n s hs
    rcases hs with hs | hs
    · apply (hb n s hs).trans
      apply mul_le_mul (le_add_of_nonneg_right hD)
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hB (le_max_left _ _) _) (by positivity))
        (by positivity) (by positivity)
    · apply (he n s hs).trans
      apply mul_le_mul (le_add_of_nonneg_left hC)
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hE (le_max_right _ _) _) (by positivity))
        (by positivity) (by positivity)
  · intro s hs
    obtain ⟨U,hU,hsU,C₀,B,hC,hB,hb⟩ := exteriorEven_local_exponential_constants (hsub hs)
    exact ⟨U,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hsU),C₀,B,hC,hB,hb⟩

/-- The exact scale displayed in Appendix C, uniform on any compact exterior set. -/
theorem compact_exteriorEven_sqrt_bound {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ n s, s ∈ K →
      ‖exteriorEvenTerm n s‖ ≤ C₀*(C/Real.sqrt (2*(n+1)))^(2*(n+1)) := by
  obtain ⟨C₀,B,hC,hB,hb⟩ := compact_exteriorEven_exponential_constants hK hsub
  refine ⟨C₀,2*(Real.exp 1*B+1),hC,by positivity,?_⟩
  intro n s hs
  exact (hb n s hs).trans (mul_le_mul_of_nonneg_left
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      factorial_majorant_le_sqrt (n+1) (by omega) hB) hC)

/-- Fixed Cauchy derivative losses with the same compact root-test scale. -/
theorem compact_exteriorEven_cauchy_sqrt_bound {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ exteriorDomain) :
    ∃ C₀ C d : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ 0 < d ∧ ∀ j n s, s ∈ K →
      ‖iteratedDeriv j (exteriorEvenTerm n) s‖ ≤
        (j.factorial:ℝ)*d⁻¹^j*C₀*(C/Real.sqrt (2*(n+1)))^(2*(n+1)) := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open exteriorDomain_isOpen hsub
  obtain ⟨C₀,C,hC₀,hC,hb⟩ := compact_exteriorEven_sqrt_bound hK.cthickening hdsub
  refine ⟨C₀,C,d,hC₀,hC,hd,?_⟩
  intro j n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => exteriorEvenTerm_analyticAt n (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; simp only [div_eq_mul_inv,inv_pow]; ring

/-- The exact compact Cauchy majorant is summable over the manuscript's
positive even orders, with any fixed derivative order. -/
theorem even_cauchy_sqrt_majorant_summable (C C₀ d : ℝ) (j : ℕ) :
    Summable (fun n : ℕ => (j.factorial:ℝ)*d⁻¹^j*C₀*
      (C/Real.sqrt (2*(n+1)))^(2*(n+1))) := by
  have hs := (cauchy_sqrt_majorant_summable C C₀ d j).comp_injective
    (show Function.Injective (fun n : ℕ => 2*(n+1)) from by
      intro a b h
      dsimp at h
      omega)
  simpa only [Function.comp_def,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hs

end
end IsingBulk.Tail
