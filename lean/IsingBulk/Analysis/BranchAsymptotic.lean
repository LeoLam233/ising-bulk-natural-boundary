import IsingBulk.Analysis.BranchQuotients

/-! Quantitative thresholds imply the source's uniform asymptotic regimes. -/
namespace IsingBulk.Branch
noncomputable section
open Filter

theorem ratio_atTop_eventually_threshold {ι : Type*} (l : Filter ι) (ε M : ι → ℝ)
    (hε : ∀ᶠ i in l, 0 < ε i) (hlim : Tendsto (fun i => M i/ε i) l atTop) (R : ℝ) :
    ∀ᶠ i in l, R*ε i ≤ M i := by
  filter_upwards [hε,hlim.eventually (eventually_ge_atTop R)] with i hi hratio
  exact (le_div_iff₀ hi).mp hratio

theorem OriginalQuotientData.separated_eventually {d : LocalBranchData} (B : OriginalQuotientData d)
    {ι : Type*} (l : Filter ι) (ε m M : ι → ℝ)
    (hdom : ∀ᶠ i in l, 0 < ε i ∧ ε i < B.r ∧ 0 ≤ m i ∧ m i ≤ M i/2 ∧ M i < B.r)
    (hlim : Tendsto (fun i => M i/ε i) l atTop) :
    ∀ᶠ i in l,
      (min (B.k/4) (B.a/2))/Real.sqrt (m i+ε i) ≤
        deriv (originalRealPhase d (ε i)) (m i)-deriv (originalRealPhase d (ε i)) (M i) ∧
      0 < deriv (originalRealPhase d (ε i)) (m i)-deriv (originalRealPhase d (ε i)) (M i) ∧
      ‖deriv (originalPhase d (ε i)) (m i)*deriv (originalPhase d (ε i)) (M i)‖ /
        (deriv (originalRealPhase d (ε i)) (m i)-deriv (originalRealPhase d (ε i)) (M i)) ≤
        (B.C^2/min (B.k/4) (B.a/2))/Real.sqrt (M i) := by
  have ht := ratio_atTop_eventually_threshold l ε M (hdom.mono fun _ h => h.1) hlim B.separationThreshold
  filter_upwards [hdom,ht] with i hi ht
  exact ⟨B.separated_difference _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 ht,
    B.separated_quotient _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 ht⟩

theorem OriginalQuotientData.comparable_eventually {d : LocalBranchData} (B : OriginalQuotientData d)
    {ι : Type*} (l : Filter ι) (ε m M : ι → ℝ)
    (hdom : ∀ᶠ i in l, 0 < ε i ∧ ε i < B.r ∧ M i/2 < m i ∧ m i < M i ∧ M i < B.r)
    (hlim : Tendsto (fun i => m i/ε i) l atTop) :
    ∀ᶠ i in l,
      0 < deriv (originalRealPhase d (ε i)) (m i)-deriv (originalRealPhase d (ε i)) (M i) ∧
      ‖deriv (originalPhase d (ε i)) (m i)*deriv (originalPhase d (ε i)) (M i)‖ /
        (deriv (originalRealPhase d (ε i)) (m i)-deriv (originalRealPhase d (ε i)) (M i)) ≤
        (2*B.C^2/B.k)*Real.sqrt (M i)/(M i-m i) := by
  have ht := ratio_atTop_eventually_threshold l ε m (hdom.mono fun _ h => h.1) hlim B.C₀
  filter_upwards [hdom,ht] with i hi ht
  exact B.comparable_quotient _ _ _ hi.1 hi.2.1 ht hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2

end
end IsingBulk.Branch
