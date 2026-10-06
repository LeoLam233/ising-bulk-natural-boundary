import IsingBulk.Tail.ProtectedDensity
import IsingBulk.First.SourceAuxiliaryRegularity

/-! Actual angular current derivatives at fixed radius and fixed lambda.
The moving lambda split is absent from every differentiation statement. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

theorem actualNamedCurrentIntegral_analytic_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    AnalyticOnNhd ℂ (actualNamedCurrentIntegral N f r τ lam q) (dampingDomain r) ∧
      ∀ k : ℕ, ∀ s ∈ dampingDomain r,
        iteratedDeriv k (actualNamedCurrentIntegral N f r τ lam q) s =
          ∫ θ in angleBox N, iteratedDeriv k (fun z => namedCurrentDensity f r τ lam z q θ) s := by
  let U := dampingDomain r
  let psi := deformedPoint (N := N) f r τ lam
  let chi := namedCurrentAngularWeight N f τ lam q
  let F := continuedContourDensity N
  let G := fun z : ℂ => ∫ θ in angleBox N, chi θ*F (z,psi θ)
  have hU : IsOpen U := dampingDomain_isOpen r
  have hpsi : Continuous psi := deformedPoint_continuous f r τ lam hp.continuous hm.continuous
  have hchi : Continuous chi := namedCurrentAngularWeight_continuous N f τ lam q hp hm ha
  have hupper (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) (i : Fin N) :
      0 < (sourceW s (deformedPoint f r τ lam θ i)).im := by
    have hbase := sourceW_upper_of_margin hr hr1 hs.2 (deformedPoint_zero_norm f hr.le τ θ i)
    exact hbase.trans_le (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp0 hm0 hps hms i)
  have hY (θ : Fin N → ℝ) : 1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0 :=
    homotopy_y_gap_nonzero hN f hr hr1 hτ hlam θ hp0 hm1
  have hZ (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) :
      1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0 := by
    apply one_sub_coordinateProduct_ne_zero hN
    intro i
    unfold selectedContinuedRoot
    rw [continuedRoot_eq_interiorRoot (hupper s hs θ i)]
    exact interiorRoot_norm_lt_one (hupper s hs θ i)
  have hF (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) (_hθ : θ ∈ angleBox N) :
      AnalyticAt ℂ F (s,psi θ) :=
    continuedContourDensity_analyticAt (p := (s,psi θ)) hs.1
      (deformedPoint_nonzero f hr.ne' τ lam θ)
      (fun i => Or.inl (Or.inl (hupper s hs θ i))) (hY θ) (hZ s hs θ)
  have hpoint (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) :
      namedCurrentDensity f r τ lam s q θ=chi θ*F (s,psi θ) := by
    rw [← continuedNamedCurrentDensity_weighted f r τ lam s q θ]
    unfold continuedNamedCurrentDensity namedCurrentDensity
    rw [continuedPulledDensity_eq_original f r τ lam s θ (hupper s hs θ)]
  have heq (s : ℂ) (hs : s ∈ U) :
      actualNamedCurrentIntegral N f r τ lam q =ᶠ[𝓝 s] G := by
    filter_upwards [hU.mem_nhds hs] with z hz
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    exact hpoint z hz θ
  constructor
  · intro s hs
    have hg := compact_analytic_shape_integral_analyticAt (μ := volume) isCompact_Icc hU F
      psi hpsi chi hchi hF hs
    exact hg.congr (heq s hs).symm
  · intro k s hs
    have hjet := compact_analytic_shape_integral_iteratedDeriv (μ := volume) isCompact_Icc hU F
      psi hpsi chi hchi hF k s hs
    calc
      _ = iteratedDeriv k G s := (heq s hs).iteratedDeriv_eq k
      _ = ∫ θ in angleBox N, chi θ*iteratedDeriv k (fun z => F (z,psi θ)) s := by
        simpa only [iteratedDeriv_eq_iterate,G,angleBox] using hjet
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro θ _hθ
        have he : (fun z => namedCurrentDensity f r τ lam z q θ) =ᶠ[𝓝 s]
            (fun z => chi θ*F (z,psi θ)) := by
          filter_upwards [hU.mem_nhds hs] with z hz
          exact hpoint z hz θ
        have he' := he.iteratedDeriv_eq k
        rw [iteratedDeriv_const_mul_field] at he'
        exact he'.symm

/-- The manuscript's J_{N,j}(lambda), with every s derivative inside the
angular current integral, is the true derivative of the current slice. -/
theorem actualCurrentSlice_iteratedDeriv (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0)
    (k : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv k (actualCurrentSlice N f r τ lam) s =
      differentiatedCurrentSlice N f r τ lam k s := by
  have hj (q : Fin N) := actualNamedCurrentIntegral_analytic_jets N hN f hr hr1 hτ hlam q
    hp hm ha hp0 hm0 hm1 hps hms
  unfold actualCurrentSlice differentiatedCurrentSlice
  rw [iteratedDeriv_fun_sum (fun q _ => ((hj q).1 s hs).contDiffAt)]
  apply Finset.sum_congr rfl
  intro q _
  exact (hj q).2 k s hs

/-- Retains the literal fixed smooth Stokes multiplier in the derivative
normalization; no lambda endpoint is differentiated. -/
theorem differentiatedCurrentSlice_source_formula (N : ℕ) (f : SelectorFunctions)
    (r τ lam : ℝ) (j : ℕ) (s : ℂ) :
    differentiatedCurrentSlice N f r τ lam j s =
      ∑ q : Fin N, ∫ θ in angleBox N,
        (-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ))*
          iteratedDeriv j (fun z => pulledDensity f r τ lam z θ) s := by
  unfold differentiatedCurrentSlice namedCurrentDensity
  simp only [iteratedDeriv_const_mul_field]

end
end IsingBulk.Tail
