import IsingBulk.Anisotropic.FormFactors.AnalyticSeriesJets

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Filter
open scoped Topology

theorem selected_particleSeries_comp_hasSum_iteratedDeriv
    (lam : ℝ) (N k : ℕ → ℕ) (hN : ∀ n, 0<N n) (hk : ∀ n, k n≤N n)
    (hs : ∀ C : ℝ, 0≤C → Summable (fun n => hadamardEnvelope C (N n)))
    {zeta : ℂ → ℂ} {u : ℂ} (ha : AnalyticAt ℂ zeta u) (hz : zeta u∉spectralSet lam) (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^(k n)*
      unscaledFullCoefficient (N n) lam (zeta v)) u)
      (iteratedDeriv j (fun v => ∑' n, (spectralProduct lam (zeta v))^(k n)*
        unscaledFullCoefficient (N n) lam (zeta v)) u) := by
  obtain ⟨D,C,hD,hC,he⟩ := local_fullCoefficient_envelope hz
  let P : ℝ := ‖spectralProduct lam (zeta u)‖+2
  have hP : 1≤P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam (zeta u))]
  have hp : ∀ᶠ v in 𝓝 u, ‖spectralProduct lam (zeta v)‖≤P := by
    have hh : ∀ᶠ v in 𝓝 u, ‖spectralProduct lam (zeta v)‖<P :=
      (((spectralProduct_analyticAt_ff lam (zeta u)).comp (f := zeta) ha).continuousAt.norm.eventually_lt
        continuousAt_const (by dsimp [P]; linarith))
    exact hh.mono (fun _ hv => hv.le)
  have hevent : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ zeta v ∧ zeta v∉spectralSet lam ∧
      ∀ n, ‖(spectralProduct lam (zeta v))^(k n)*unscaledFullCoefficient (N n) lam (zeta v)‖≤
        D*hadamardEnvelope (C*P) (N n) := by
    filter_upwards [ha.eventually_analyticAt,ha.continuousAt.tendsto.eventually he,hp,
      ha.continuousAt.tendsto.eventually ((spectralSet_isClosed lam).isOpen_compl.mem_nhds hz)] with v hv he hp hz
    exact ⟨hv,hz,fun n => weighted_envelope hD.le hC.le hP (hk n) hp (he (N n) (hN n))⟩
  obtain ⟨U,hUsub,hU,hu⟩ := mem_nhds_iff.mp hevent
  apply hasSum_iteratedDeriv_of_summable_envelope hU _
    ((hs (C*P) (by positivity)).mul_left D) (fun n v hv => (hUsub hv).2.2 n) j hu
  intro n v hv
  have haa := (hUsub hv).1
  exact (((spectralProduct_analyticAt_ff lam (zeta v)).comp (f := zeta) haa).pow (k n)).mul
    ((unscaledFullCoefficient_analyticOnNhd (N n) (hN n) lam (zeta v) (hUsub hv).2.1).comp
      (f := zeta) haa)

theorem high_particleSeries_comp_hasSum_iteratedDeriv (lam : ℝ)
    {zeta : ℂ → ℂ} {u : ℂ} (ha : AnalyticAt ℂ zeta u) (hz : zeta u∉spectralSet lam) (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^n*
      unscaledFullCoefficient (2*n+1) lam (zeta v)) u)
      (iteratedDeriv j (fun v => ∑' n, (spectralProduct lam (zeta v))^n*
        unscaledFullCoefficient (2*n+1) lam (zeta v)) u) :=
  selected_particleSeries_comp_hasSum_iteratedDeriv lam (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hC => hadamardEnvelope_odd_summable hC) ha hz j

theorem low_particleSeries_comp_hasSum_iteratedDeriv (lam : ℝ)
    {zeta : ℂ → ℂ} {u : ℂ} (ha : AnalyticAt ℂ zeta u) (hz : zeta u∉spectralSet lam) (j : ℕ) :
    HasSum (fun n => iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^(n+1)*
      unscaledFullCoefficient (2*n+2) lam (zeta v)) u)
      (iteratedDeriv j (fun v => ∑' n, (spectralProduct lam (zeta v))^(n+1)*
        unscaledFullCoefficient (2*n+2) lam (zeta v)) u) := by
  apply selected_particleSeries_comp_hasSum_iteratedDeriv lam (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega) _ ha hz j
  intro C hC
  have hh := (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
  change Summable (fun n => hadamardEnvelope C (2*(n+1))) at hh
  simpa only [mul_add,mul_one] using hh

end
end IsingBulk.Anisotropic.FormFactors
