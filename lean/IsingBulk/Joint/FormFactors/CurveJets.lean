import IsingBulk.Joint.FormFactors.NormalConvergence

/-! Arbitrary holomorphic transverse-curve attachment of the complete physical
particle series, with an arbitrary analytic amplitude. All derivative sums
are obtained from the joint normal envelopes, not assumed as a bridge. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter
open scoped Topology
open IsingBulk.Anisotropic.FormFactors (hadamardEnvelope hadamardEnvelope_odd_summable)

theorem selected_curve_local_envelope (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {curve : ℂ → Coupling} {amp : ℂ → ℂ} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (ha : AnalyticAt ℂ amp u) (hu : curve u ∉ spectralSet) :
    ∃ V ∈ 𝓝 u, IsOpen V ∧
      (∀ n (j : ℕ) v, v ∈ V → ContDiffAt ℂ j
        (fun t => amp t * particleTerm N k n (curve t)) v) ∧
      ∃ M : ℕ → ℝ, Summable M ∧
        ∀ n v, v ∈ V → ‖amp v * particleTerm N k n (curve v)‖ ≤ M n := by
  obtain ⟨U,hUK,hU,hUc,M,hM,hb⟩ := local_weighted_envelope N k hN hk hs hu
  have hamp : ∀ᶠ v in 𝓝 u, ‖amp v‖ ≤ ‖amp u‖+1 :=
    (ha.continuousAt.norm.eventually_lt continuousAt_const (by linarith)).mono (fun _ h => h.le)
  have he : ∀ᶠ v in 𝓝 u, curve v ∈ U ∧ AnalyticAt ℂ curve v ∧
      AnalyticAt ℂ amp v ∧ ‖amp v‖ ≤ ‖amp u‖+1 :=
    (hc.continuousAt.tendsto.eventually hUK).and
      (hc.eventually_analyticAt.and (ha.eventually_analyticAt.and hamp))
  obtain ⟨V,hVsub,hV,huV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hV.mem_nhds huV,hV,?_,fun n => (‖amp u‖+1)*M n,hM.mul_left _,?_⟩
  · intro n j v hv
    exact (hVsub hv).2.2.1.contDiffAt.mul
      ((particleTerm_contDiffAt N k hN n j (hUc (hVsub hv).1)).comp v (hVsub hv).2.1.contDiffAt)
  · intro n v hv
    rw [norm_mul]
    exact mul_le_mul (hVsub hv).2.2.2 (hb n (curve v) (hVsub hv).1)
      (norm_nonneg _) (by positivity)

theorem selected_particleSeries_mul_comp_hasSum_iteratedDeriv (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {curve : ℂ → Coupling} {amp : ℂ → ℂ} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (ha : AnalyticAt ℂ amp u) (hu : curve u ∉ spectralSet)
    (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun t => amp t * particleTerm N k n (curve t)) u)
      (iteratedDeriv j (fun t => amp t * ∑' n, particleTerm N k n (curve t)) u) := by
  obtain ⟨V,hVu,hV,hf,M,hM,hb⟩ := selected_curve_local_envelope N k hN hk hs hc ha hu
  have hh := normalSeries_iteratedFDeriv_hasSum j hV hf hM hb (mem_of_mem_nhds hVu)
  have hm := (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin j) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hh
  simpa only [iteratedDeriv_eq_equiv_comp,Function.comp_apply,tsum_mul_left] using! hm

theorem high_particleSeries_mul_comp_hasSum_iteratedDeriv
    {curve : ℂ → Coupling} {amp : ℂ → ℂ} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (ha : AnalyticAt ℂ amp u) (hu : curve u ∉ spectralSet)
    (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun t => amp t *
        (p (curve t)^n * unscaledFullCoefficient (2*n+1) (curve t))) u)
      (iteratedDeriv j (fun t => amp t *
        ∑' n : ℕ, p (curve t)^n * unscaledFullCoefficient (2*n+1) (curve t)) u) :=
  selected_particleSeries_mul_comp_hasSum_iteratedDeriv (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hC => hadamardEnvelope_odd_summable hC) hc ha hu j

theorem low_particleSeries_mul_comp_hasSum_iteratedDeriv
    {curve : ℂ → Coupling} {amp : ℂ → ℂ} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (ha : AnalyticAt ℂ amp u) (hu : curve u ∉ spectralSet)
    (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun t => amp t *
        (p (curve t)^(n+1) * unscaledFullCoefficient (2*n+2) (curve t))) u)
      (iteratedDeriv j (fun t => amp t *
        ∑' n : ℕ, p (curve t)^(n+1) * unscaledFullCoefficient (2*n+2) (curve t)) u) :=
  selected_particleSeries_mul_comp_hasSum_iteratedDeriv (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
    (fun _ hC => even_positive_hadamard_summable hC) hc ha hu j

end
end IsingBulk.Joint.FormFactors
