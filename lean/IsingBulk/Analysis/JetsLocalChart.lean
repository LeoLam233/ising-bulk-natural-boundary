import IsingBulk.Analysis.JetsFiniteSum
import IsingBulk.Analysis.LieLocal

/-! Fixed low-dimensional coefficient neighborhoods and local angular charts.
The coefficient conditions include the selected diagonal. Only the angular
regular chart excludes the genuine selected and kernel poles. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch IsingBulk.Lie
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd analytic_coordinate

structure CoefficientPoint {N : ℕ} (p q : Fin N) (z : ℂ × (Fin N → ℂ)) : Prop where
  a : ∀ i, AnalyticAt ℂ (fun t : ℂ × ℂ => regularA t.1 t.2) (z.1,z.2 i)
  g : ∀ i, AnalyticAt ℂ (fun t : ℂ × ℂ => regularG t.1 t.2) (z.1,z.2 i)
  den : AnalyticAt ℂ (fun t : ℂ × ℂ × ℂ => selectedDenominator t.1 t.2.1 t.2.2)
    (z.1,z.2 p,z.2 q)
  den_ne : selectedDenominator z.1 (z.2 p) (z.2 q) ≠ 0
  gsum_ne : regularG z.1 (z.2 p)+regularG z.1 (z.2 q) ≠ 0

theorem CoefficientPoint.regular_numerators {N : ℕ} {p q : Fin N}
    {z : ℂ × (Fin N → ℂ)} (h : CoefficientPoint p q z) :
    (∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) z) ∧
    (∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z) := by
  have hA : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) z := by
    intro i
    exact AnalyticAt.comp (g := fun t : ℂ × ℂ => regularA t.1 t.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i)) (h.a i)
      (analyticAt_fst.prod (analytic_coordinate i z))
  have hG : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularG t.1 (t.2 i)) z := by
    intro i
    exact AnalyticAt.comp (g := fun t : ℂ × ℂ => regularG t.1 t.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i)) (h.g i)
      (analyticAt_fst.prod (analytic_coordinate i z))
  have hD : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => selectedDenominator t.1 (t.2 p) (t.2 q)) z :=
    AnalyticAt.comp (g := fun t : ℂ × ℂ × ℂ => selectedDenominator t.1 t.2.1 t.2.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 p,t.2 q)) h.den
      (analyticAt_fst.prod ((analytic_coordinate p z).prod (analytic_coordinate q z)))
  have hH : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => selectedRegularFactor t.1 (t.2 p) (t.2 q)) z :=
    ((hG p).mul (hG q)).div hD h.den_ne
  have hsum : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => aSum t.1 t.2) z :=
    Finset.analyticAt_fun_sum _ fun i _ => hA i
  constructor <;> intro i
  · unfold fieldRegularNumerator
    split_ifs <;> fun_prop (disch := exact h.den_ne)
  · unfold residualRegularNumerator
    split_ifs <;> fun_prop

theorem CoefficientPoint.continuity {N : ℕ} {p q : Fin N}
    {z : ℂ × (Fin N → ℂ)} (h : CoefficientPoint p q z) :
    ContinuousAt (fun t : ℂ × (Fin N → ℂ) => regularG t.1 (t.2 p)+regularG t.1 (t.2 q)) z ∧
    ContinuousAt (fun t : ℂ × (Fin N → ℂ) => selectedDenominator t.1 (t.2 p) (t.2 q)) z := by
  have hG : ∀ i, ContinuousAt (fun t : ℂ × (Fin N → ℂ) => regularG t.1 (t.2 i)) z := by
    intro i
    exact ContinuousAt.comp (g := fun t : ℂ × ℂ => regularG t.1 t.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i)) (h.g i).continuousAt (by fun_prop)
  refine ⟨(hG p).add (hG q), ?_⟩
  exact ContinuousAt.comp (g := fun t : ℂ × ℂ × ℂ => selectedDenominator t.1 t.2.1 t.2.2)
    (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 p,t.2 q)) h.den.continuousAt (by fun_prop)

theorem coefficient_neighborhoods (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    ∃ U : Set (ℂ × ℂ), ∃ P : Set (ℂ × ℂ × ℂ),
      IsOpen U ∧ (s,0) ∈ U ∧ IsOpen P ∧ (s,0,0) ∈ P ∧
      ∀ N : ℕ, ∀ p q : Fin N, ∀ z : ℂ × (Fin N → ℂ),
        (∀ i, (z.1,z.2 i) ∈ U) → (z.1,z.2 p,z.2 q) ∈ P → CoefficientPoint p q z := by
  have ha := regularA_analytic_base s c hs hS hc
  have hg := regularG_analytic_base s c hs hS hc
  have hd := selectedDenominator_analytic_base s c hs hS hc
  obtain ⟨U,hU,hUo,hsU⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and hg.eventually_analyticAt)
  have hpair := (selected_factors_eventually s c hs hS hc).and hd.eventually_analyticAt
  obtain ⟨P,hP,hPo,hsP⟩ := eventually_nhds_iff.mp hpair
  refine ⟨U,P,hUo,hsU,hPo,hsP,?_⟩
  intro N p q z hz hp
  exact ⟨fun i => (hU _ (hz i)).1, fun i => (hU _ (hz i)).2,
    (hP _ hp).2, (hP _ hp).1.2.2.2.1, (hP _ hp).1.2.2.1⟩

/-- Conditions for the actual expression, independent of recurrence depth.
In contrast to CoefficientPoint, this explicitly excludes genuine poles. -/
structure ActualJetPoint {n : ℕ} (v θ : ℝ) (p q : Fin (n+1)) (s : ℂ)
    (x : AngularSpace n) : Prop where
  coefficient : CoefficientPoint p q (s,chartMap v θ s x)
  s_ne : s ≠ 0
  re_pos : ∀ i, 0 < (chartW s v θ (x i)).re
  im_pos : ∀ i, 0 < (chartW s v θ (x i)).im
  g_pos : ∀ i, 0 < (angularG v θ (x i)).re
  sin_ne : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0
  b_ne : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0
  slit : ∀ i, 1-(s+s⁻¹-Complex.cos (chartPhase s v θ (x i)))^2 ∈ Complex.slitPlane
  y_den : ∀ i, 1-(regularY s (chartPhase s v θ (x i)))^(-2:ℤ) ≠ 0
  delta_ne : chartMap v θ s x q-chartMap v θ s x p ≠ 0
  kernel_ne : regularKernel s (chartMap v θ s x) ≠ 0

theorem ActualJetPoint.g_ne {n : ℕ} {v θ : ℝ} {p q : Fin (n+1)} {s : ℂ}
    {x : AngularSpace n} (h : ActualJetPoint v θ p q s x) :
    ∀ i, regularG s (chartMap v θ s x i) ≠ 0 := by
  intro i
  rw [chartMap, regularG_chartPhase s v θ (x i) (h.g_pos i)]
  intro hz
  simpa [hz] using h.g_pos i

end
end IsingBulk.Jets
