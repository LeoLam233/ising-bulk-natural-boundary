import IsingBulk.Joint.FormFactors.NormalConvergence
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Normal convergence on every compact subset, including every fixed mixed
complex derivative of the actual normalized full-particle sums. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter
open scoped Topology
open IsingBulk.Anisotropic.FormFactors (hadamardEnvelope hadamardEnvelope_odd_summable)

theorem selected_normalized_local_data (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {amp : Coupling → ℂ} {K : Coupling} (ha : AnalyticAt ℂ amp K)
    (hK : K ∉ spectralSet) :
    ∃ V ∈ 𝓝 K, IsOpen V ∧
      (∀ n (j : ℕ) L, L ∈ V → ContDiffAt ℂ j (fun t => amp t * particleTerm N k n t) L) ∧
      ∃ M : ℕ → ℝ, Summable M ∧
        ∀ n L, L ∈ V → ‖amp L * particleTerm N k n L‖ ≤ M n := by
  obtain ⟨U,hUK,hU,hUc,M,hM,hb⟩ := local_weighted_envelope N k hN hk hs hK
  have hamp : ∀ᶠ L in 𝓝 K, ‖amp L‖ ≤ ‖amp K‖+1 :=
    (ha.continuousAt.norm.eventually_lt continuousAt_const (by linarith)).mono (fun _ h => h.le)
  have he : ∀ᶠ L in 𝓝 K, L ∈ U ∧ AnalyticAt ℂ amp L ∧ ‖amp L‖ ≤ ‖amp K‖+1 :=
    (show ∀ᶠ L in 𝓝 K, L ∈ U from hUK).and (ha.eventually_analyticAt.and hamp)
  obtain ⟨V,hVsub,hV,hKV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hV.mem_nhds hKV,hV,?_,fun n => (‖amp K‖+1)*M n,hM.mul_left _,?_⟩
  · intro n j L hL
    exact (hVsub hL).2.1.contDiffAt.mul (particleTerm_contDiffAt N k hN n j (hUc (hVsub hL).1))
  · intro n L hL
    rw [norm_mul]
    exact mul_le_mul (hVsub hL).2.2 (hb n L (hVsub hL).1) (norm_nonneg _) (by positivity)

theorem selected_normalized_all_mixed_derivatives (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {amp : Coupling → ℂ} {K : Coupling} (ha : AnalyticAt ℂ amp K)
    (hK : K ∉ spectralSet) (j : ℕ) :
    HasSum (fun n => iteratedFDeriv ℂ j (fun t => amp t * particleTerm N k n t) K)
      (iteratedFDeriv ℂ j (fun t => amp t * ∑' n, particleTerm N k n t) K) := by
  obtain ⟨V,hVK,hV,hf,M,hM,hb⟩ := selected_normalized_local_data N k hN hk hs ha hK
  simpa only [tsum_mul_left] using normalSeries_iteratedFDeriv_hasSum j hV hf hM hb (mem_of_mem_nhds hVK)

theorem selected_normalized_locallyUniform_jets (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {amp : Coupling → ℂ} {D : Set Coupling} (ha : AnalyticOnNhd ℂ amp D)
    (hD : D ⊆ spectralSetᶜ) (j : ℕ) :
    TendstoLocallyUniformlyOn
      (fun m K => ∑ n ∈ Finset.range m, iteratedFDeriv ℂ j (fun t => amp t * particleTerm N k n t) K)
      (iteratedFDeriv ℂ j (fun t => amp t * ∑' n, particleTerm N k n t)) atTop D := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro K hK
  obtain ⟨U,hUK,hU,hf,M,hM,hb⟩ := selected_normalized_local_data N k hN hk hs (ha K hK) (hD hK)
  obtain ⟨V,hVK,_,hVU,M',hM',hb'⟩ := normalSeries_local_jet_bound j hU hf hM hb (mem_of_mem_nhds hUK)
  refine ⟨V,mem_nhdsWithin_of_mem_nhds hVK,?_⟩
  apply (tendstoUniformlyOn_tsum_nat hM' hb').congr_right
  intro L hL
  have hh := (normalSeries_iteratedFDeriv_hasSum j hU hf hM hb (hVU hL)).tsum_eq
  simpa only [tsum_mul_left] using hh

theorem selected_normalized_uniform_jets_on_compact (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    {amp : Coupling → ℂ} {D C : Set Coupling} (ha : AnalyticOnNhd ℂ amp D)
    (hD : D ⊆ spectralSetᶜ) (hC : IsCompact C) (hCD : C ⊆ D) (j : ℕ) :
    TendstoUniformlyOn
      (fun m K => ∑ n ∈ Finset.range m, iteratedFDeriv ℂ j (fun t => amp t * particleTerm N k n t) K)
      (iteratedFDeriv ℂ j (fun t => amp t * ∑' n, particleTerm N k n t)) atTop C :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp
    ((selected_normalized_locallyUniform_jets N k hN hk hs ha hD j).mono hCD)

theorem highNormalizedBulk_all_mixed_derivatives {K : Coupling} (hK : K ∈ highDomain) (j : ℕ) :
    HasSum (fun n => iteratedFDeriv ℂ j
      (fun t => highPrefactor t * (p t^n * unscaledFullCoefficient (2*n+1) t)) K)
      (iteratedFDeriv ℂ j highNormalizedBulk K) :=
  selected_normalized_all_mixed_derivatives (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hC => hadamardEnvelope_odd_summable hC) (highPrefactor_analyticOnNhd K hK)
    (highDomain_subset_spectralComplement hK) j

theorem lowNormalizedBulk_all_mixed_derivatives {K : Coupling} (hK : K ∈ lowDomain) (j : ℕ) :
    HasSum (fun n => iteratedFDeriv ℂ j
      (fun t => lowPrefactor t * (p t^(n+1) * unscaledFullCoefficient (2*n+2) t)) K)
      (iteratedFDeriv ℂ j lowNormalizedBulk K) :=
  selected_normalized_all_mixed_derivatives (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
    (fun _ hC => even_positive_hadamard_summable hC) (lowPrefactor_analyticOnNhd K hK)
    (lowDomain_subset_spectralComplement hK) j

theorem highNormalizedBulk_uniform_jets_on_compact {C : Set Coupling}
    (hC : IsCompact C) (hCD : C ⊆ highDomain) (j : ℕ) :
    TendstoUniformlyOn (fun m K => ∑ n ∈ Finset.range m, iteratedFDeriv ℂ j
      (fun t => highPrefactor t * (p t^n * unscaledFullCoefficient (2*n+1) t)) K)
      (iteratedFDeriv ℂ j highNormalizedBulk) atTop C :=
  selected_normalized_uniform_jets_on_compact (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hB => hadamardEnvelope_odd_summable hB) highPrefactor_analyticOnNhd
    highDomain_subset_spectralComplement hC hCD j

theorem lowNormalizedBulk_uniform_jets_on_compact {C : Set Coupling}
    (hC : IsCompact C) (hCD : C ⊆ lowDomain) (j : ℕ) :
    TendstoUniformlyOn (fun m K => ∑ n ∈ Finset.range m, iteratedFDeriv ℂ j
      (fun t => lowPrefactor t * (p t^(n+1) * unscaledFullCoefficient (2*n+2) t)) K)
      (iteratedFDeriv ℂ j lowNormalizedBulk) atTop C :=
  selected_normalized_uniform_jets_on_compact (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
    (fun _ hB => even_positive_hadamard_summable hB) lowPrefactor_analyticOnNhd
    lowDomain_subset_spectralComplement hC hCD j

/-- A finite compact cover adds local summable envelopes into one literal
compact normal majorant; uniform convergence alone is not used as a proxy. -/
theorem compact_normal_majorant_of_local
    {E G : Type} [NormedAddCommGroup E] [NormedAddCommGroup G]
    {f : ℕ → E → G} {C : Set E} (hC : IsCompact C)
    (hlocal : ∀ x∈C, ∃ V∈𝓝 x, IsOpen V ∧ ∃ M : ℕ → ℝ,
      Summable M ∧ ∀ n y, y∈V → ‖f n y‖≤M n) :
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n x, x∈C → ‖f n x‖≤M n := by
  classical
  choose V hVx hV M hM hb using (fun x : C => hlocal x x.2)
  have hMpos (x : C) (n : ℕ) : 0≤M x n :=
    (norm_nonneg _).trans (hb x n x (mem_of_mem_nhds (hVx x)))
  obtain ⟨t,ht⟩ := hC.elim_finite_subcover V hV (fun x hx =>
    mem_iUnion.mpr ⟨⟨x,hx⟩,mem_of_mem_nhds (hVx ⟨x,hx⟩)⟩)
  refine ⟨fun n => ∑ x∈t, M x n,?_,?_,?_⟩
  · exact summable_sum (s := t) (fun x _ => hM x)
  · intro n
    exact Finset.sum_nonneg (fun x _ => hMpos x n)
  · intro n x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact (hb y n x hxy).trans (Finset.single_le_sum (fun y _ => hMpos y n) hy)

theorem selected_normalized_compact_normal_majorant (N k : ℕ → ℕ)
    (hN : ∀ n, 0<N n) (hk : ∀ n, k n≤N n)
    (hs : ∀ B : ℝ, 0≤B → Summable (fun n => hadamardEnvelope B (N n)))
    {amp : Coupling → ℂ} {D C : Set Coupling} (ha : AnalyticOnNhd ℂ amp D)
    (hD : D⊆spectralSetᶜ) (hC : IsCompact C) (hCD : C⊆D) (j : ℕ) :
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n K, K∈C →
      ‖iteratedFDeriv ℂ j (fun t => amp t*particleTerm N k n t) K‖≤M n := by
  apply compact_normal_majorant_of_local hC
  intro K hK
  obtain ⟨U,hUK,hU,hf,M,hM,hb⟩ := selected_normalized_local_data N k hN hk hs
    (ha K (hCD hK)) (hD (hCD hK))
  obtain ⟨V,hVK,hV,_,M',hM',hb'⟩ := normalSeries_local_jet_bound j hU hf hM hb (mem_of_mem_nhds hUK)
  exact ⟨V,hVK,hV,M',hM',hb'⟩

theorem highNormalizedBulk_compact_normal_majorant {C : Set Coupling}
    (hC : IsCompact C) (hCD : C⊆highDomain) (j : ℕ) :
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n K, K∈C →
      ‖iteratedFDeriv ℂ j
        (fun t => highPrefactor t*(p t^n*unscaledFullCoefficient (2*n+1) t)) K‖≤M n :=
  selected_normalized_compact_normal_majorant (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hB => hadamardEnvelope_odd_summable hB) highPrefactor_analyticOnNhd
    highDomain_subset_spectralComplement hC hCD j

theorem lowNormalizedBulk_compact_normal_majorant {C : Set Coupling}
    (hC : IsCompact C) (hCD : C⊆lowDomain) (j : ℕ) :
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n K, K∈C →
      ‖iteratedFDeriv ℂ j
        (fun t => lowPrefactor t*(p t^(n+1)*unscaledFullCoefficient (2*n+2) t)) K‖≤M n :=
  selected_normalized_compact_normal_majorant (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
    (fun _ hB => even_positive_hadamard_summable hB) lowPrefactor_analyticOnNhd
    lowDomain_subset_spectralComplement hC hCD j

end
end IsingBulk.Joint.FormFactors
