import IsingBulk.Analysis.JetsNormBounds

namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators Topology ContDiff
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq ι]

/-- Local analytic version of the sharp multiset Leibniz norm estimate. -/
theorem analytic_product_multiset_jet_bound (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (k : ℕ) (ha : ∀ i ∈ s, AnalyticAt ℂ (f i) x) :
    ‖iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms : ℝ) *
        ∏ i ∈ s, ‖iteratedFDeriv ℂ (Multiset.count i p) (f i) x‖ := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, AnalyticAt ℂ (f i) y := by
    exact (Filter.eventually_all_finset s).2 (fun i hi => (ha i hi).eventually_analyticAt)
  obtain ⟨U,hU,hopen,hx⟩ := eventually_nhds_iff.mp he
  have hc : ∀ i ∈ s, ContDiffOn ℂ ω (f i) U :=
    fun i hi y hy => (hU y hy i hi).contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_prod_le hc hopen.uniqueDiffOn hx
    (n := k) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

lemma sym_countPerms_sum (s : Finset ι) (k : ℕ) :
    ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms : ℝ) = (s.card : ℝ)^k := by
  simpa using (Finset.sum_pow (s := s) (fun _ : ι => (1 : ℝ)) k).symm

/-- At most k changed factors cost C^k. The complete surviving product keeps B,
including exact zeros; no division by a factor occurs. -/
theorem analytic_product_changed_factors_bound (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (C B : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (ha : ∀ i ∈ s, AnalyticAt ℂ (f i) x)
    (hj : ∀ i ∈ s, ∀ k, 0 < k → k ≤ J → ‖iteratedFDeriv ℂ k (f i) x‖ ≤ C)
    (hremain : ∀ t ⊆ s, t.card ≤ J → ∏ i ∈ s \ t, ‖f i x‖ ≤ B)
    (k : ℕ) (hk : k ≤ J) :
    ‖iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      (s.card : ℝ)^k * C^k * B := by
  apply (analytic_product_multiset_jet_bound s f x k ha).trans
  have hterm : ∀ p ∈ s.sym k,
      ∏ i ∈ s, ‖iteratedFDeriv ℂ (Multiset.count i p) (f i) x‖ ≤ C^k*B := by
    intro p hp
    let t := (p : Multiset ι).toFinset
    have hts : t ⊆ s := by
      intro i hi
      exact Finset.mem_sym_iff.mp hp i (by simpa [t] using hi)
    have htk : t.card ≤ k := by
      exact (Multiset.toFinset_card_le _).trans_eq p.property
    have htj := htk.trans hk
    have hchanged : ∏ i ∈ t, ‖iteratedFDeriv ℂ (Multiset.count i p) (f i) x‖ ≤ C^t.card := by
      calc
        _ ≤ ∏ _i ∈ t, C := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i hi
          apply hj i (hts hi) _
          · exact Multiset.count_pos.mpr (by simpa [t] using hi)
          · exact (Multiset.count_le_card i p).trans (by simpa using hk)
        _ = _ := by simp
    have hsame : ∏ i ∈ s \ t, ‖iteratedFDeriv ℂ (Multiset.count i p) (f i) x‖ =
        ∏ i ∈ s \ t, ‖f i x‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hn : i ∉ (p : Multiset ι) := by simpa [t] using (Finset.mem_sdiff.mp hi).2
      rw [Multiset.count_eq_zero.mpr hn]
      exact norm_iteratedFDeriv_zero
    rw [← Finset.prod_sdiff hts, hsame]
    calc
      _ ≤ B*C^t.card := mul_le_mul (hremain t hts htj) hchanged
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hB
      _ ≤ B*C^k := by gcongr
      _ = C^k*B := mul_comm _ _
  calc
    _ ≤ ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms : ℝ) * (C^k*B) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hterm p hp) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sym_countPerms_sum]; ring

section RealSmooth
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Real smooth version of the sharp multiset Leibniz norm estimate. -/
theorem smooth_product_multiset_jet_bound (s : Finset ι) (f : ι → F → ℂ)
    (x : F) (k : ℕ) (ha : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms : ℝ) *
        ∏ i ∈ s, ‖iteratedFDeriv ℝ (Multiset.count i p) (f i) x‖ := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ (k:ℕ∞ω) (f i) y := by
    exact (Filter.eventually_all_finset s).2 (fun i hi => ((ha i hi).of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp))
  obtain ⟨U,hU,hopen,hx⟩ := eventually_nhds_iff.mp he
  have hc : ∀ i ∈ s, ContDiffOn ℝ (k:ℕ∞ω) (f i) U :=
    fun i hi y hy => (hU y hy i hi).contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_prod_le hc hopen.uniqueDiffOn hx
    (n := k) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

/-- At most k changed factors cost C^k. The complete surviving product keeps B,
including exact zeros; no division by a factor occurs. -/
theorem smooth_product_changed_factors_bound (s : Finset ι) (f : ι → F → ℂ)
    (x : F) (J : ℕ) (C B : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (ha : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x)
    (hj : ∀ i ∈ s, ∀ k, 0 < k → k ≤ J → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C)
    (hremain : ∀ t ⊆ s, t.card ≤ J → ∏ i ∈ s \ t, ‖f i x‖ ≤ B)
    (k : ℕ) (hk : k ≤ J) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      (s.card : ℝ)^k * C^k * B := by
  apply (smooth_product_multiset_jet_bound s f x k ha).trans
  have hterm : ∀ p ∈ s.sym k,
      ∏ i ∈ s, ‖iteratedFDeriv ℝ (Multiset.count i p) (f i) x‖ ≤ C^k*B := by
    intro p hp
    let t := (p : Multiset ι).toFinset
    have hts : t ⊆ s := by
      intro i hi
      exact Finset.mem_sym_iff.mp hp i (by simpa [t] using hi)
    have htk : t.card ≤ k := by
      exact (Multiset.toFinset_card_le _).trans_eq p.property
    have htj := htk.trans hk
    have hchanged : ∏ i ∈ t, ‖iteratedFDeriv ℝ (Multiset.count i p) (f i) x‖ ≤ C^t.card := by
      calc
        _ ≤ ∏ _i ∈ t, C := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i hi
          apply hj i (hts hi) _
          · exact Multiset.count_pos.mpr (by simpa [t] using hi)
          · exact (Multiset.count_le_card i p).trans (by simpa using hk)
        _ = _ := by simp
    have hsame : ∏ i ∈ s \ t, ‖iteratedFDeriv ℝ (Multiset.count i p) (f i) x‖ =
        ∏ i ∈ s \ t, ‖f i x‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hn : i ∉ (p : Multiset ι) := by simpa [t] using (Finset.mem_sdiff.mp hi).2
      rw [Multiset.count_eq_zero.mpr hn]
      exact norm_iteratedFDeriv_zero
    rw [← Finset.prod_sdiff hts, hsame]
    calc
      _ ≤ B*C^t.card := mul_le_mul (hremain t hts htj) hchanged
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hB
      _ ≤ B*C^k := by gcongr
      _ = C^k*B := mul_comm _ _
  calc
    _ ≤ ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms : ℝ) * (C^k*B) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hterm p hp) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sym_countPerms_sum]; ring

end RealSmooth

end
end IsingBulk.Tail
