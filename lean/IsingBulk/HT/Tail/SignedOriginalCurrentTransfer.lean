import IsingBulk.HT.Tail.SignedLargeCurrentTransfer

/-! Complete signed original-disk current Cauchy and fixed real-window integration.
The epsilon-dependent split is never differentiated. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Metric MeasureTheory
open scoped Topology BigOperators

theorem signed_actualCurrentSlice_analytic_on_damping (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam) :
    AnalyticOnNhd ℂ (signedActualCurrentSlice σ N f r τ lam) (dampingDomain r) := by
  intro s hs
  apply Finset.analyticAt_fun_sum
  intro q _
  exact (signed_actualNamedCurrentIntegral_analytic_jets σ hσ N hN f hr hr1 hτ hlam q
    hf.p_smooth hf.m_smooth hf.a_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero).1 s hs

theorem signed_actual_current_original_disk_cauchy (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    {s : ℂ} {δ B : ℝ} (hδ : 0<δ)
    (hsub : closedBall s δ ⊆ dampingDomain r)
    (hbound : ∀ z ∈ closedBall s δ, ‖signedContinuedCurrentSlice σ N f r τ lam z‖≤B) (j : ℕ) :
    ‖signedDifferentiatedCurrentSlice σ N f r τ lam j s‖ ≤ (j.factorial:ℝ)*B/δ^j := by
  have hb : ∀ z ∈ closedBall s δ, ‖signedActualCurrentSlice σ N f r τ lam z‖≤B := by
    intro z hz
    have hm := (hsub hz).2
    rw [← (signed_continuedCurrentSlice_eventually_actual σ N hN f hr hr1 hτ hlam hm
      hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero).eq_of_nhds]
    exact hbound z hz
  rw [← signed_actualCurrentSlice_iteratedDeriv σ hσ N hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth hf.a_smooth
    hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j (hsub (mem_closedBall_self hδ.le))]
  exact cauchy_bound_on_subdisk ((signed_actualCurrentSlice_analytic_on_damping σ hσ N hN f hf hr hr1 hτ hlam).mono hsub)
    hb hδ subset_rfl j

theorem signed_actual_small_current_original_disk_integral (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ)
    {s : ℂ} {δ B lamStar : ℝ} (hδ : 0<δ) (hB : 0≤B) (hls0 : 0≤lamStar) (hls1 : lamStar≤1)
    (hsub : closedBall s δ ⊆ dampingDomain r)
    (hbound : ∀ lam ∈ Icc (0:ℝ) 1, ∀ z ∈ closedBall s δ,
      ‖signedContinuedCurrentSlice σ N f r τ lam z‖≤B) (j : ℕ) :
    IntervalIntegrable (fun lam => signedDifferentiatedCurrentSlice σ N f r τ lam j s) volume 0 lamStar ∧
      ‖∫ lam in 0..lamStar, signedDifferentiatedCurrentSlice σ N f r τ lam j s‖ ≤ (j.factorial:ℝ)*B/δ^j := by
  have hi := (signed_currentIntegral_iteratedDeriv_integrable σ hσ N hN f hr hr1 hτ hf.p_smooth hf.m_smooth
    hf.a_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j
    (hsub (mem_closedBall_self hδ.le))).1
  refine ⟨hi.mono_set ?_,?_⟩
  · rw [uIcc_of_le hls0,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hls1
  · have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := lamStar)
      (C := (j.factorial:ℝ)*B/δ^j) (f := fun lam => signedDifferentiatedCurrentSlice σ N f r τ lam j s) (by
        intro lam hlam
        rw [uIoc_of_le hls0] at hlam
        have hl : lam ∈ Icc (0:ℝ) 1 := ⟨hlam.1.le,hlam.2.trans hls1⟩
        exact signed_actual_current_original_disk_cauchy σ hσ N hN f hf hr hr1 hτ hl.1 hδ hsub (hbound lam hl) j)
    simp only [sub_zero,abs_of_nonneg hls0] at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) hls1)

end
end IsingBulk.HT.Tail
