import IsingBulk.First.CompactParameterIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! All-order differentiation under a possibly noncompact integral. A genuine
L1 majorant for the analytic integrand on an open complex neighborhood yields
L1 bounds for every derivative by Cauchy's estimate on smaller disks. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

theorem analyticAt_iteratedDeriv {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j f) s := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem cauchy_bound_on_subdisk {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ s ∈ U, AnalyticAt ℂ f s) {b : ℝ} (hb : ∀ s ∈ U, ‖f s‖ ≤ b)
    {s : ℂ} {d : ℝ} (hd : 0 < d) (hsub : closedBall s d ⊆ U) (j : ℕ) :
    ‖iteratedDeriv j f s‖ ≤ j.factorial*b/d^j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hd
  · apply DifferentiableOn.diffContOnCl
    intro t ht
    exact (hf t (hsub (closure_ball_subset_closedBall ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    exact hb t (hsub (sphere_subset_closedBall ht))

theorem dominated_analytic_integral_jets {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (F : ℂ → A → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ a, ∀ t ∈ U, AnalyticAt ℂ (fun z => F z a) t)
    (hmeas : ∀ j t, t ∈ U → AEStronglyMeasurable (fun a => iteratedDeriv j (fun z => F z a) t) μ)
    (b : A → ℝ) (hb : Integrable b μ)
    (hbound : ∀ᵐ a ∂μ, ∀ t ∈ U, ‖F t a‖ ≤ b a)
    {s : ℂ} (hs : s ∈ U) (j : ℕ) :
    Integrable (fun a => iteratedDeriv j (fun z => F z a) s) μ ∧
    HasDerivAt (fun t => ∫ a, iteratedDeriv j (fun z => F z a) t ∂μ)
      (∫ a, iteratedDeriv (j+1) (fun z => F z a) s ∂μ) s := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hs)
  have hd : 0 < ε/4 := by linarith
  have hsub {t : ℂ} (ht : t ∈ ball s (ε/4)) : closedBall t (ε/4) ⊆ U := by
    apply Subset.trans _ hεU
    apply closedBall_subset_ball'
    have hh : dist t s < ε/4 := ht
    linarith
  have hhere : s ∈ ball s (ε/4) := mem_ball_self hd
  have hsmall : ball s (ε/4) ⊆ U := fun t ht => hsub ht (mem_closedBall_self hd.le)
  have hbnd (n : ℕ) : Integrable (fun a => (n.factorial:ℝ)*b a/(ε/4)^n) μ :=
    (hb.const_mul (n.factorial:ℝ)).div_const _
  have hjint : Integrable (fun a => iteratedDeriv j (fun z => F z a) s) μ := by
    apply (hbnd j).mono' (hmeas j s hs)
    filter_upwards [hbound] with a ha
    exact cauchy_bound_on_subdisk (hhol a) ha hd (hsub hhere) j
  refine ⟨hjint, ?_⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hd)
    (Filter.Eventually.mono (ball_mem_nhds s hd) (fun t ht => hmeas j t (hsmall ht)))
    hjint (hmeas (j+1) s hs) ?_ (hbnd (j+1)) ?_).2
  · filter_upwards [hbound] with a ha
    intro t ht
    exact cauchy_bound_on_subdisk (hhol a) ha hd (hsub ht) (j+1)
  · apply Filter.Eventually.of_forall
    intro a t ht
    simpa only [iteratedDeriv_succ] using
      (analyticAt_iteratedDeriv (hhol a t (hsmall ht)) j).differentiableAt.hasDerivAt

/-- The conclusion is about the true iterated complex derivative and genuine
Bochner integrability of every integrated jet, with no compactness assumption. -/
theorem iteratedDeriv_integral_of_dominated_analytic {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (F : ℂ → A → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ a, ∀ t ∈ U, AnalyticAt ℂ (fun z => F z a) t)
    (hmeas : ∀ j t, t ∈ U → AEStronglyMeasurable (fun a => iteratedDeriv j (fun z => F z a) t) μ)
    (b : A → ℝ) (hb : Integrable b μ)
    (hbound : ∀ᵐ a ∂μ, ∀ t ∈ U, ‖F t a‖ ≤ b a)
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    iteratedDeriv j (fun t => ∫ a, F t a ∂μ) s =
      ∫ a, iteratedDeriv j (fun z => F z a) s ∂μ := by
  induction j generalizing s with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    have he : iteratedDeriv j (fun t => ∫ a, F t a ∂μ) =ᶠ[𝓝 s]
        (fun t => ∫ a, iteratedDeriv j (fun z => F z a) t ∂μ) := by
      filter_upwards [hU.mem_nhds hs] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (dominated_analytic_integral_jets F hU hhol hmeas b hb hbound hs j).2.deriv

end
end IsingBulk.First
