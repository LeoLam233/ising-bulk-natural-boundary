import IsingBulk.First.CompactIntegralHolomorphic
import IsingBulk.Anisotropic.NegativeCycles.FixedDiskCauchyJets

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric MeasureTheory

/-- A compact actual parameter integral inherits its full disk and its Cauchy
bound. A restricted measure can encode a fixed measurable angular partition. -/
theorem compact_remainder_analytic_jets
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    (F : ℂ × E → ℂ) (psi : X → E) (hpsi : Continuous psi)
    {r M : ℝ} (hr : 0<r)
    (hF : ∀ t∈ball 0 r, ∀ x∈K, AnalyticAt ℂ F (t,psi x))
    (hb : ∀ t∈ball 0 r, ∀ x∈K, ‖F (t,psi x)‖≤M) :
    AnalyticOnNhd ℂ (fun t => ∫ x in K, F (t,psi x) ∂μ) (ball 0 r) ∧
    (∀ j : ℕ, ‖iteratedDeriv j (fun t => ∫ x in K, F (t,psi x) ∂μ) 0 /
        (j.factorial:ℂ)‖≤((μ K).toReal*M)/(r/2)^j) ∧
    (∀ j : ℕ, iteratedDeriv j (fun t => ∫ x in K, F (t,psi x) ∂μ) 0 =
      ∫ x in K, iteratedDeriv j (fun t => F (t,psi x)) 0 ∂μ) := by
  have ha : AnalyticOnNhd ℂ (fun t => ∫ x in K, F (t,psi x) ∂μ) (ball 0 r) := by
    intro t ht
    simpa only [one_mul] using IsingBulk.First.compact_analytic_shape_integral_analyticAt
      hK isOpen_ball F psi hpsi (fun _ => 1) continuous_const hF ht
  have hbound : ∀ t∈ball 0 r, ‖∫ x in K, F (t,psi x) ∂μ‖≤(μ K).toReal*M := by
    intro t ht
    let _ : IsFiniteMeasure (μ.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top⟩
    have hh := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
      ((ae_restrict_mem hK.measurableSet).mono (hb t ht))
    simpa only [Measure.real,Measure.restrict_apply_univ,mul_comm] using hh
  refine ⟨ha,analytic_disk_normalized_jet_bound hr ha hbound,?_⟩
  intro j
  have hh := IsingBulk.First.compact_analytic_shape_integral_iteratedDeriv (μ := μ) hK isOpen_ball
    F psi hpsi (fun _ => 1) continuous_const hF j 0 (by simpa using hr)
  simpa only [one_mul,iteratedDeriv_eq_iterate] using hh

end
end IsingBulk.Anisotropic.NegativeCycles
