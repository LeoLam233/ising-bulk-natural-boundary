import IsingBulk.HT.Final.RightOnsiteSeries
import IsingBulk.HT.Final.OnsiteSymmetry
import IsingBulk.Tail.ExteriorFormFactors

/-! The actual onsite source on the left trace chart. Its parity is proved
at the contour level; no parity of the full odd HT coefficient is assumed. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

theorem rightOnsiteFormFactor_conjugate (N : ℕ) (s : ℂ) :
    rightOnsiteFormFactor N (star s) = star (rightOnsiteFormFactor N s) := by
  have hr : rightCanonicalRadius (star s) = rightCanonicalRadius s := by
    simp [rightCanonicalRadius]
  simp only [rightOnsiteFormFactor,hr,onsiteFormFactor_conjugate]

def leftOnsiteFormFactor (N : ℕ) (s : ℂ) : ℂ :=
  (-1:ℂ)^N * rightOnsiteFormFactor N (-s)

def leftOnsiteOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, leftOnsiteFormFactor (2*n+1) s

theorem leftOnsiteFormFactor_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftOnsiteFormFactor N s = onsiteFormFactor N r s := by
  have hn : 1+r⁻¹ < (sourceS (-s)).re := by
    simpa only [sourceS_neg,Complex.neg_re] using hm
  have hsign : (-1:ℂ)^N*(-1:ℂ)^N = 1 := by rw [← mul_pow]; norm_num
  rw [leftOnsiteFormFactor,rightOnsiteFormFactor_eq_fixed_radius N hN hr hr1 hn,
    onsiteFormFactor_neg,← mul_assoc,hsign,one_mul]

theorem leftOnsiteFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : (sourceS s).re < -2) : AnalyticAt ℂ (leftOnsiteFormFactor N) s := by
  have hn : 2 < (sourceS (-s)).re := by
    simp only [sourceS_neg,Complex.neg_re]; linarith
  exact (analyticAt_const (v := (-1:ℂ)^N)).mul
    ((rightOnsiteFormFactor_analyticAt N hN hn).comp analyticAt_id.neg)

theorem leftOnsiteFormFactor_conjugate (N : ℕ) (s : ℂ) :
    leftOnsiteFormFactor N (star s) = star (leftOnsiteFormFactor N s) := by
  have h := rightOnsiteFormFactor_conjugate N (-s)
  simp only [star_neg] at h
  simpa only [leftOnsiteFormFactor,star_mul,star_pow,star_neg,star_one,mul_comm] using
    congrArg (fun z : ℂ => (-1:ℂ)^N*z) h

theorem leftOnsiteFormFactor_eq_upper (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    leftOnsiteFormFactor N s = upperOnsiteFormFactor N s := by
  have hn : 2 < (sourceS (-s)).re := by
    simp only [sourceS_neg,Complex.neg_re]; linarith
  obtain ⟨hr,hr1,hmr⟩ := rightCanonicalRadius_admissible hn
  obtain ⟨hu0,hu1,hmu⟩ := canonicalRadius_admissible hu
  let R := max (rightCanonicalRadius (-s)) (canonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_left _ _)
  have hR1 : R < 1 := max_lt hr1 hu1
  have hir : R⁻¹ ≤ (rightCanonicalRadius (-s))⁻¹ := inv_anti₀ hr (le_max_left _ _)
  have hiu : R⁻¹ ≤ (canonicalRadius s)⁻¹ := inv_anti₀ hu0 (le_max_right _ _)
  have hmrR : 1+R⁻¹ < -(sourceS s).re := by
    simp only [sourceS_neg,Complex.neg_re] at hmr
    linarith
  have hmuR : R⁻¹-R < (sourceS s).im := by
    have := le_max_right (rightCanonicalRadius (-s)) (canonicalRadius s)
    change canonicalRadius s ≤ R at this
    linarith
  rw [leftOnsiteFormFactor_eq_fixed_radius N hN hR hR1 hmrR,
    upperOnsiteFormFactor_eq_fixed_radius N hN hR hR1 hmuR]

theorem leftOnsiteOddSeries_eq_neg_right (s : ℂ) :
    leftOnsiteOddSeries s = -rightOnsiteOddSeries (-s) := by
  simp only [leftOnsiteOddSeries,leftOnsiteFormFactor,rightOnsiteOddSeries]
  have hp (n : ℕ) : (-1:ℂ)^(2*n+1) = -1 := by
    exact (show Odd (2*n+1) from ⟨n,rfl⟩).neg_one_pow
  simp_rw [hp,neg_one_mul]
  exact tsum_neg

theorem leftOnsiteOddSeries_analyticAt {s : ℂ} (hs : (sourceS s).re < -2) :
    AnalyticAt ℂ leftOnsiteOddSeries s := by
  have hn : 2 < (sourceS (-s)).re := by
    simp only [sourceS_neg,Complex.neg_re]; linarith
  have he : leftOnsiteOddSeries = (fun t => -rightOnsiteOddSeries (-t)) :=
    funext leftOnsiteOddSeries_eq_neg_right
  rw [he]
  exact ((rightOnsiteOddSeries_analyticAt hn).comp analyticAt_id.neg).neg

/-- A genuine compact normal majorant obtained by reflection of the actual
right onsite source integral, including the one-particle term. -/
theorem compact_leftOnsiteOdd_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ leftTraceDomain) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖leftOnsiteFormFactor (2*n+1) s‖ ≤ u n := by
  have him : (fun s : ℂ => -s) '' K ⊆ rightTraceDomain := by
    rintro t ⟨s,hs,rfl⟩
    have hh := hsub hs
    change (sourceS s).re < -2 at hh
    change 2 < (sourceS (-s)).re
    simp only [sourceS_neg,Complex.neg_re]
    linarith
  obtain ⟨u,hu,hb⟩ := compact_rightOnsiteOdd_majorant (hK.image continuous_neg) him
  refine ⟨u,hu,?_⟩
  intro n s hs
  have hp : (-1:ℂ)^(2*n+1) = -1 := (show Odd (2*n+1) from ⟨n,rfl⟩).neg_one_pow
  simpa only [leftOnsiteFormFactor,hp,neg_one_mul,norm_neg] using
    hb n (-s) ⟨s,hs,rfl⟩

theorem leftOnsiteOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftOnsiteOddSeries s = ∑' n : ℕ, onsiteFormFactor (2*n+1) r s := by
  apply tsum_congr
  intro n
  exact leftOnsiteFormFactor_eq_fixed_radius _ (by omega) hr hr1 hm

theorem leftOnsiteOdd_local_normal {s : ℂ} (hs : (sourceS s).re < -2) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ leftTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖leftOnsiteFormFactor (2*n+1) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (leftTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ leftTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_leftOnsiteOdd_majorant (isCompact_closedBall s (ε/2)) hK
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

theorem compact_leftOnsiteOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ leftTraceDomain) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n s, s ∈ K →
      ‖iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) s‖ ≤ u n := by
  obtain ⟨d,hd,hdsub⟩ := hK.exists_cthickening_subset_open leftTraceDomain_isOpen hsub
  obtain ⟨u,hu,hb⟩ := compact_leftOnsiteOdd_majorant (hK.cthickening) hdsub
  refine ⟨fun n => ((j.factorial:ℝ)/d^j)*u n, hu.mul_left _, ?_⟩
  intro n s hs
  have hc := cauchy_bound_on_subdisk
    (fun t ht => leftOnsiteFormFactor_analyticAt (2*n+1) (by omega) (hdsub ht))
    (fun t ht => hb n t ht) hd (closedBall_subset_cthickening hs d) j
  convert hc using 1; ring

theorem leftOnsiteOdd_derivative_local_normal (j : ℕ) {s : ℂ}
    (hs : (sourceS s).re < -2) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ leftTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ U →
        ‖iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) t‖ ≤ u n := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (leftTraceDomain_isOpen.mem_nhds hs)
  have hK : closedBall s (ε/2) ⊆ leftTraceDomain :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨u,hu,hb⟩ := compact_leftOnsiteOdd_derivative_majorant (isCompact_closedBall s (ε/2)) hK j
  refine ⟨ball s (ε/2),isOpen_ball,mem_ball_self (by positivity),
    ball_subset_closedBall.trans hK,u,hu,?_⟩
  exact fun n t ht => hb n t (ball_subset_closedBall ht)

/-- Termwise differentiation of the literal canonical odd series, at every
fixed order and every point of its left-trace domain. -/
theorem leftOnsiteOddSeries_iteratedDeriv (j : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    iteratedDeriv j leftOnsiteOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := leftOnsiteOdd_derivative_local_normal j hs
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (analyticAt_iteratedDeriv
        (leftOnsiteFormFactor_analyticAt (2*n+1) (by omega) (hsub ht)) j).differentiableAt.differentiableWithinAt)
      hU hb hsU
    have he : (fun t => ∑' n : ℕ, iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) t)
        =ᶠ[𝓝 s] iteratedDeriv j leftOnsiteOddSeries := by
      filter_upwards [hU.mem_nhds hsU] with t ht
      exact (ih (hsub ht)).symm
    have hh' := hh.tsum_eq
    rw [he.deriv_eq] at hh'
    simpa only [iteratedDeriv_succ] using hh'.symm

/-- Absolute convergence at every fixed derivative order. -/
theorem leftOnsiteOdd_derivative_summable (j : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) s‖) := by
  obtain ⟨U,_hU,hsU,_hsub,u,hu,hb⟩ := leftOnsiteOdd_derivative_local_normal j hs
  exact hu.of_norm_bounded (fun n => by simpa only [norm_norm] using hb n s hsU)


end
end IsingBulk.HT.Final
