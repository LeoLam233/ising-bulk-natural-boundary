import IsingBulk.Anisotropic.RegularEdges.LeadingMultiplier
import IsingBulk.Anisotropic.FormFactors.AnalyticSeriesJets

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.FormFactors Set Filter
open scoped Topology BigOperators

/-- One actual singular term survives finite-order selection and a summably bounded tail. -/
theorem scaled_series_first_limit {a L p : ℕ} (ha : 0<a) (hp : p<L)
    {f : ℕ→ℝ→ℂ} {F : ℝ→ℂ} {C : ℂ}
    (hs : ∀ᶠ t : ℝ in 𝓝[>] 0,HasSum (fun n => f n t) (F t))
    (hfirst : ∀n<L,Tendsto (fun t : ℝ => (t^a) • f n t)
      (𝓝[>] 0) (𝓝 (if n=p then C else 0)))
    {G : ℕ→ℝ} (hG : Summable G)
    (htail : ∀ᶠ t : ℝ in 𝓝[>] 0,∀n,‖f (n+L) t‖≤G n) :
    Tendsto (fun t : ℝ => (t^a) • F t) (𝓝[>] 0) (𝓝 C) := by
  have hb : ∃ D : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,‖∑' n,f (n+L) t‖≤D := by
    refine ⟨∑' n,G n,?_⟩
    filter_upwards [htail] with t ht
    have hn := hG.of_nonneg_of_le (fun _ => norm_nonneg _) ht
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum ht hn hG)
  have hzero := bounded_jet_scaled_zero ha hb
  have hfinite := tendsto_finsetSum (Finset.range L)
    (fun n hn => hfirst n (Finset.mem_range.mp hn))
  simp only [Finset.sum_ite_eq',Finset.mem_range,hp,ite_true] at hfinite
  have hh := hfinite.add hzero
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hs] with t ht
  rw [←ht.tsum_eq,←ht.summable.sum_add_tsum_nat_add L,smul_add,Finset.smul_sum]

/-- Local normal convergence exchanges all actual parameter derivatives after an analytic
chart and a common analytic multiplier. -/
theorem selected_chart_series_hasSum_jets {lam : ℝ} {U : Set ℂ} {zeta A : ℂ→ℂ}
    (hU : IsOpen U) (hzeta : AnalyticOnNhd ℂ zeta U) (hA : AnalyticOnNhd ℂ A U)
    (hz : ∀u∈U,zeta u∉spectralSet lam) (N k : ℕ→ℕ)
    (hN : ∀n,0<N n) (hk : ∀n,k n≤N n)
    (henv : ∀C : ℝ,0≤C → Summable (fun n => hadamardEnvelope C (N n)))
    (j : ℕ) {u : ℂ} (hu : u∈U) :
    HasSum (fun n => iteratedDeriv j (fun v => A v*(spectralProduct lam (zeta v))^(k n)*
      unscaledFullCoefficient (N n) lam (zeta v)) u)
      (iteratedDeriv j (fun v => ∑' n,A v*(spectralProduct lam (zeta v))^(k n)*
        unscaledFullCoefficient (N n) lam (zeta v)) u) := by
  obtain ⟨D,C,hD,hC,hev⟩ := local_fullCoefficient_envelope (hz u hu)
  let P : ℝ := ‖spectralProduct lam (zeta u)‖+2
  let M : ℝ := ‖A u‖+1
  have hP : 1≤P := by dsimp [P]; linarith [norm_nonneg (spectralProduct lam (zeta u))]
  have hM : 0<M := by dsimp [M]; positivity
  have hp : ∀ᶠ v in 𝓝 u,‖spectralProduct lam (zeta v)‖≤P := by
    apply (((spectralProduct_analyticAt_ff lam (zeta u)).comp (hzeta u hu)).continuousAt.norm.eventually_lt
      continuousAt_const (show ‖spectralProduct lam (zeta u)‖<P by dsimp [P]; linarith)).mono
    exact fun _ h => h.le
  have hm : ∀ᶠ v in 𝓝 u,‖A v‖≤M := by
    apply ((hA u hu).continuousAt.norm.eventually_lt continuousAt_const
      (show ‖A u‖<M by dsimp [M]; linarith)).mono
    exact fun _ h => h.le
  have hall : ∀ᶠ v in 𝓝 u,v∈U ∧ ∀n,
      ‖A v*(spectralProduct lam (zeta v))^(k n)*unscaledFullCoefficient (N n) lam (zeta v)‖≤
        (M*D)*hadamardEnvelope (C*P) (N n) := by
    filter_upwards [hU.mem_nhds hu,(hzeta u hu).continuousAt.tendsto.eventually hev,hp,hm]
      with v hv hve hvp hvm
    refine ⟨hv,fun n => ?_⟩
    have hb := weighted_envelope hD.le hC.le hP (hk n) hvp (hve (N n) (hN n))
    rw [mul_assoc,norm_mul]
    calc
      _ ≤ M*(D*hadamardEnvelope (C*P) (N n)) :=
        mul_le_mul hvm hb (norm_nonneg _) hM.le
      _ = _ := by ring
  obtain ⟨V,hVsub,hV,huV⟩ := mem_nhds_iff.mp hall
  apply hasSum_iteratedDeriv_of_summable_envelope hV _
    ((henv (C*P) (by positivity)).mul_left (M*D)) (fun n v hv => (hVsub hv).2 n) j huV
  intro n v hv
  have hvU := (hVsub hv).1
  exact (((hA v hvU).mul (((spectralProduct_analyticAt_ff lam (zeta v)).comp
    (hzeta v hvU)).pow (k n))).mul
    ((unscaledFullCoefficient_analyticOnNhd (N n) (hN n) lam (zeta v) (hz v hvU)).comp (hzeta v hvU)))

end
end IsingBulk.Anisotropic.RegularEdges
