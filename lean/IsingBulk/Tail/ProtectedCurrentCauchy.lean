import IsingBulk.Tail.ProtectedCurrentDisk
import IsingBulk.Tail.GlobalAnalytic

/-! Actual J_{N,j} Cauchy wiring. The remaining undifferentiated norm envelope
is a visible premise; this transfer theorem is not the large-current bound. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Metric
open scoped ContDiff

theorem actual_current_cauchy_on_continued_disk (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im) {δ B : ℝ} (hδ : 0 < δ)
    (hhol : AnalyticOnNhd ℂ (continuedCurrentSlice N f r τ lam) (closedBall s δ))
    (hbound : ∀ z ∈ closedBall s δ, ‖continuedCurrentSlice N f r τ lam z‖ ≤ B) (j : ℕ) :
    ‖differentiatedCurrentSlice N f r τ lam j s‖ ≤ (j.factorial:ℝ)*B/δ^j := by
  have hs := dampingDomain_of_margin hr hr1 hmargin
  rw [← actualCurrentSlice_iteratedDeriv N hN f hr hr1 hτ hlam hp hm ha hp0 hm0 hm1 hps hms j hs]
  exact cauchy_bound_of_continued_germ
    (continuedCurrentSlice_eventually_actual N hN f hr hr1 hτ hlam hmargin hp0 hm0 hps hms).symm
    hhol hbound hδ subset_rfl j

end
end IsingBulk.Tail
