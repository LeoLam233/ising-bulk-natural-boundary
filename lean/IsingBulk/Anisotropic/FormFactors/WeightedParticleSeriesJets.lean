import IsingBulk.Anisotropic.FormFactors.ParticleSeriesJets

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Filter
open scoped Topology

theorem high_particleSeries_mul_comp_hasSum_iteratedDeriv (lam : ℝ)
    {A zeta : ℂ → ℂ} {u : ℂ} (hA : AnalyticAt ℂ A u)
    (ha : AnalyticAt ℂ zeta u) (hz : zeta u∉spectralSet lam) (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun v => A v*((spectralProduct lam (zeta v))^n*
      unscaledFullCoefficient (2*n+1) lam (zeta v))) u)
      (iteratedDeriv j (fun v => A v*(∑' n, (spectralProduct lam (zeta v))^n*
        unscaledFullCoefficient (2*n+1) lam (zeta v))) u) := by
  obtain ⟨D,C,hD,hC,he⟩ := local_fullCoefficient_envelope hz
  let P : ℝ := ‖spectralProduct lam (zeta u)‖+2
  let Q : ℝ := ‖A u‖+1
  have hP : 1≤P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam (zeta u))]
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hp : ∀ᶠ v in 𝓝 u, ‖spectralProduct lam (zeta v)‖≤P := by
    have hh : ∀ᶠ v in 𝓝 u, ‖spectralProduct lam (zeta v)‖<P :=
      (((spectralProduct_analyticAt_ff lam (zeta u)).comp (f := zeta) ha).continuousAt.norm.eventually_lt
        continuousAt_const (by dsimp [P]; linarith))
    exact hh.mono (fun _ hv => hv.le)
  have hq : ∀ᶠ v in 𝓝 u, ‖A v‖≤Q := by
    have hh : ∀ᶠ v in 𝓝 u, ‖A v‖<Q :=
      hA.continuousAt.norm.eventually_lt continuousAt_const (by dsimp [Q]; linarith)
    exact hh.mono (fun _ hv => hv.le)
  have hevent : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ A v ∧ AnalyticAt ℂ zeta v ∧ zeta v∉spectralSet lam ∧
      ∀ n, ‖A v*((spectralProduct lam (zeta v))^n*unscaledFullCoefficient (2*n+1) lam (zeta v))‖≤
        Q*(D*hadamardEnvelope (C*P) (2*n+1)) := by
    filter_upwards [hA.eventually_analyticAt,ha.eventually_analyticAt,ha.continuousAt.tendsto.eventually he,hp,hq,
      ha.continuousAt.tendsto.eventually ((spectralSet_isClosed lam).isOpen_compl.mem_nhds hz)] with v hvA hv he hp hq hz
    refine ⟨hvA,hv,hz,?_⟩
    intro n
    rw [norm_mul]
    exact mul_le_mul hq (weighted_envelope hD.le hC.le hP (by omega : n≤2*n+1) hp
      (he (2*n+1) (by omega))) (norm_nonneg _) hQ.le
  obtain ⟨U,hUsub,hU,hu⟩ := mem_nhds_iff.mp hevent
  have hj := hasSum_iteratedDeriv_of_summable_envelope hU
    (f := fun n v => A v*((spectralProduct lam (zeta v))^n*unscaledFullCoefficient (2*n+1) lam (zeta v)))
    (fun n v hv => (hUsub hv).1.mul
      ((((spectralProduct_analyticAt_ff lam (zeta v)).comp (f := zeta) (hUsub hv).2.1).pow n).mul
        ((unscaledFullCoefficient_analyticOnNhd (2*n+1) (by omega) lam (zeta v) (hUsub hv).2.2.1).comp
          (f := zeta) (hUsub hv).2.1)))
    (((hadamardEnvelope_odd_summable (show 0≤C*P by positivity)).mul_left D).mul_left Q)
    (fun n v hv => (hUsub hv).2.2.2 n) j hu
  simpa only [tsum_mul_left] using hj

end
end IsingBulk.Anisotropic.FormFactors
