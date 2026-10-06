import IsingBulk.Tail.ProtectedCurrentCauchy
import IsingBulk.Tail.CurrentIntervalDerivatives

/-! Cauchy and lambda integration for the literal differentiated current.
The source disk envelope remains explicit until complete-pair transfer is
attached. The split endpoint is fixed during differentiation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Metric MeasureTheory
open scoped ContDiff

theorem actual_large_current_cauchy_integral (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) {r τ : ℝ} (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0≤f.p x) (hm0 : ∀ x, 0≤f.m x) (hm1 : ∀ x, f.m x≤1)
    (hps : ∀ x, Real.sin x≤0 → f.p x=0)
    (hms : ∀ x, 0≤Real.sin x → f.m x=0)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im)
    {δ lamStar B : ℝ} (hδ : 0<δ) (hls : 0<lamStar) (hls1 : lamStar≤1) (hB : 0≤B)
    (hhol : ∀ lam ∈ Icc lamStar 1,
      AnalyticOnNhd ℂ (continuedCurrentSlice N f r τ lam) (closedBall s δ))
    (hbound : ∀ lam ∈ Icc lamStar 1, ∀ z ∈ closedBall s δ,
      ‖continuedCurrentSlice N f r τ lam z‖≤B*lam⁻¹^2) (j : ℕ) :
    IntervalIntegrable (fun lam => differentiatedCurrentSlice N f r τ lam j s) volume lamStar 1 ∧
      ‖∫ lam in lamStar..1, differentiatedCurrentSlice N f r τ lam j s‖≤
        ((j.factorial:ℝ)*B/δ^j)*lamStar⁻¹ := by
  have hfull := (currentIntegral_iteratedDeriv_integrable N hN f hr hr1 hτ hp hm ha hp0 hm0 hm1 hps hms j
    (dampingDomain_of_margin hr hr1 hmargin)).1
  refine ⟨hfull.mono_set ?_,?_⟩
  · rw [uIcc_of_le hls1,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc hls.le le_rfl
  · apply norm_large_current_integral_le hls hls1 (by positivity)
    intro lam hlam
    have hl0 : 0≤lam := hls.le.trans hlam.1.le
    have hc := actual_current_cauchy_on_continued_disk N hN f hr hr1 hτ hl0 hp hm ha hp0 hm0 hm1
      hps hms hmargin hδ (hhol lam ⟨hlam.1.le,hlam.2⟩) (hbound lam ⟨hlam.1.le,hlam.2⟩) j
    convert hc using 1
    ring

end
end IsingBulk.Tail
