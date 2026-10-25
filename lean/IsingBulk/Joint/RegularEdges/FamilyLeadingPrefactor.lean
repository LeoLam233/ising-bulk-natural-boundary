import IsingBulk.Joint.RegularEdges.FamilyLeadingLowerFull
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators

/-- The explicit epsilon-delta format and the usual uniform-limit API agree. -/
theorem family_uniform_limit_of_epsilon {E : Type*} {Q : Set E} {F : ℝ→E→ℂ} {L : E→ℂ}
    (h : ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ‖F t eta-L eta‖<ε) :
    TendstoUniformlyOn F L (𝓝[>] (0:ℝ)) Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := h ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htd
  intro eta heta
  simpa only [dist_eq_norm,norm_sub_rev] using hh eta heta t ht htd

/-- Uniform convergence, together with continuity of the limiting family,
allows the family parameter to move along the same limiting filter. -/
theorem uniform_family_joint_tendsto {E α : Type*} [TopologicalSpace E]
    {Q : Set E} {F : ℝ→E→ℂ} {L : E→ℂ}
    (hU : TendstoUniformlyOn F L (𝓝[>] (0:ℝ)) Q) (hL : ContinuousOn L Q)
    {l : Filter α} {τ : α→ℝ} {eta : α→E} {eta₀ : E}
    (hτ : Tendsto τ l (𝓝[>] 0)) (heta : Tendsto eta l (𝓝[Q] eta₀)) (heta₀ : eta₀∈Q) :
    Tendsto (fun p=>F (τ p) (eta p)) l (𝓝 (L eta₀)) := by
  have hzero : Tendsto (fun p=>F (τ p) (eta p)-L (eta p)) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hh := (Metric.tendstoUniformlyOn_iff.mp hU) ε hε
    filter_upwards [hτ.eventually hh,heta.eventually self_mem_nhdsWithin] with p hp hep
    simpa only [dist_zero_right,dist_eq_norm,norm_sub_rev,sub_zero] using hp (eta p) hep
  have hh := hzero.add ((hL eta₀ heta₀).tendsto.comp heta)
  simpa only [Function.comp_apply,zero_add,sub_add_cancel] using! hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Leibniz attachment of an actual jointly analytic external prefactor to a
complete family's leading and lower derivative limits. F may be the complete
parity susceptibility, not a finite truncation. -/
theorem compact_family_prefactor_scaled_limit {Q : Set E} (hQ : IsCompact Q)
    (A : ℂ × E→ℂ) (F : E→ℂ→ℂ) (L : E→ℂ) (k a : ℕ)
    (hA : ∀eta∈Q,AnalyticAt ℂ A (0,eta)) (hL : ContinuousOn L Q)
    (hF : ∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,ContDiffAt ℂ k (F eta) (Complex.I*(t:ℂ)^2))
    (hlead : TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv k (F eta) (Complex.I*(t:ℂ)^2))
      L (𝓝[>] (0:ℝ)) Q)
    (hlower : ∀j<k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv j (F eta) (Complex.I*(t:ℂ)^2))
      (fun _=>0) (𝓝[>] (0:ℝ)) Q) :
    TendstoUniformlyOn
      (fun (t : ℝ) eta=>(t^a) • iteratedDeriv k (fun u=>A (u,eta)*F eta u) (Complex.I*(t:ℂ)^2))
      (fun eta=>A (0,eta)*L eta) (𝓝[>] (0:ℝ)) Q := by
  apply family_uniform_limit_of_epsilon
  apply compact_joint_limit_uniform hQ
    (F:=fun p : ℝ × E => (p.1^a) • iteratedDeriv k (fun u=>A (u,p.2)*F p.2 u) (Complex.I*(p.1:ℂ)^2))
    (L:=fun eta=>A (0,eta)*L eta)
  · intro eta heta
    exact (((hA eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt.mul
      (hL eta heta))
  intro eta₀ heta₀
  let l := 𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)
  have ht : Tendsto (fun p : ℝ × E=>p.1) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1
  have he : Tendsto (fun p : ℝ × E=>p.2) l (𝓝[Q] eta₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.2
  have hu : Tendsto (fun p : ℝ × E=>Complex.I*(p.1:ℂ)^2) l (𝓝 0) := by
    simpa using! ((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (ht.mono_right nhdsWithin_le_nhds)).pow 2).const_mul Complex.I
  have hp := hu.prodMk_nhds (he.mono_right nhdsWithin_le_nhds)
  have hAj (i : ℕ) : Tendsto (fun p : ℝ × E=>iteratedDeriv i (fun u=>A (u,p.2)) (Complex.I*(p.1:ℂ)^2))
      l (𝓝 (iteratedDeriv i (fun u=>A (u,eta₀)) 0)) := by
    have hh := (jointParameterJet_analyticAt (hA eta₀ heta₀) i).continuousAt.tendsto.comp hp
    change Tendsto (fun p : ℝ × E=>jointParameterJet A i (Complex.I*(p.1:ℂ)^2,p.2))
      l (𝓝 (jointParameterJet A i (0,eta₀))) at hh
    simp_rw [jointParameterJet_eq,←iteratedDeriv_eq_iterate] at hh
    exact hh
  have hterm (i : ℕ) (hi : i∈Finset.range (k+1)) :
      Tendsto (fun p : ℝ × E=>(k.choose i:ℂ)*
        iteratedDeriv i (fun u=>A (u,p.2)) (Complex.I*(p.1:ℂ)^2)*
          ((p.1^a) • iteratedDeriv (k-i) (F p.2) (Complex.I*(p.1:ℂ)^2))) l
        (𝓝 (if i=0 then A (0,eta₀)*L eta₀ else 0)) := by
    by_cases hi0 : i=0
    · subst i
      simpa only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,iteratedDeriv_zero,ite_true] using!
        (hAj 0).mul (uniform_family_joint_tendsto hlead hL ht he heta₀)
    · have hi' := Finset.mem_range.mp hi
      have hki : k-i<k := by omega
      have hh := ((hAj i).const_mul (k.choose i:ℂ)).mul
        (uniform_family_joint_tendsto (hlower (k-i) hki) continuousOn_const ht he heta₀)
      simpa only [mul_zero,hi0,ite_false] using! hh
  have hsum := tendsto_finsetSum (Finset.range (k+1)) hterm
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,ite_true] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin,ht.eventually hF,
    hp.eventually (hA eta₀ heta₀).eventually_analyticAt] with p hmem hFp hAp
  have hAc : ContDiffAt ℂ k (fun u=>A (u,p.2)) (Complex.I*(p.1:ℂ)^2) :=
    (hAp.comp (f:=fun u : ℂ=>(u,p.2)) (analyticAt_id.prod analyticAt_const)).contDiffAt
  rw [iteratedDeriv_fun_mul hAc (hFp p.2 hmem.2),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.real_smul]
  ring

/-- Lower derivative vanishing is preserved by every actual jointly analytic
prefactor; this applies directly to the complete susceptibility family. -/
theorem compact_family_prefactor_lower_scaled_limit {Q : Set E} (hQ : IsCompact Q)
    (A : ℂ × E→ℂ) (F : E→ℂ→ℂ) (j a : ℕ)
    (hA : ∀eta∈Q,AnalyticAt ℂ A (0,eta))
    (hF : ∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,ContDiffAt ℂ j (F eta) (Complex.I*(t:ℂ)^2))
    (hlower : ∀i≤j,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv i (F eta) (Complex.I*(t:ℂ)^2))
      (fun _=>0) (𝓝[>] (0:ℝ)) Q) :
    TendstoUniformlyOn
      (fun (t : ℝ) eta=>(t^a) • iteratedDeriv j (fun u=>A (u,eta)*F eta u) (Complex.I*(t:ℂ)^2))
      (fun _=>0) (𝓝[>] (0:ℝ)) Q := by
  simpa only [mul_zero] using compact_family_prefactor_scaled_limit hQ A F (fun _=>0) j a hA
    continuousOn_const hF (hlower j le_rfl) (fun i hi=>hlower i hi.le)

end
end IsingBulk.Joint.RegularEdges
