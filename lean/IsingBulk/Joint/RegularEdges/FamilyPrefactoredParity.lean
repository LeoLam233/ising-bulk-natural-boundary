import IsingBulk.Joint.RegularEdges.FamilyPrimeLeading
import IsingBulk.Joint.RegularEdges.FamilyLeadingPrefactor

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Attach an actual analytic prefactor to all already constructed complete
parity jets. The analyticity and full series differentiation are derived here. -/
theorem compact_prefactored_parity_all_limits {b : ℝ} (B S A : ℂ × E→ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hA : ∀eta∈Q,AnalyticAt ℂ A (0,eta)) {e k a : ℕ} {L : E→ℂ}
    (hL : ContinuousOn L Q)
    (hlimits : ∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv j
      (paritySeries e b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2))
      (fun eta=>if j=k then L eta else 0) (𝓝[>] (0:ℝ)) Q) :
    ∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv j
      (fun u=>A (u,eta)*paritySeries e b (fun v=>B (v,eta)) (fun v=>S (v,eta)) u)
        (Complex.I*(t:ℂ)^2)) (fun eta=>if j=k then A (0,eta)*L eta else 0) (𝓝[>] (0:ℝ)) Q := by
  obtain ⟨δ,hδ,hjets⟩ := compact_family_paritySeries_local_jets B S hb hQ hB hS hBi hS0
  have htend : Tendsto (fun t : ℝ=>Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ=>Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hF (j : ℕ) : ∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,
      ContDiffAt ℂ j (paritySeries e b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2) := by
    filter_upwards [htend.eventually (ball_mem_nhds _ hδ),self_mem_nhdsWithin] with t ht htpos
    intro eta heta
    have hi : 0<(Complex.I*(t:ℂ)^2).im := by
      simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
      exact sq_pos_of_pos htpos
    exact (hjets eta heta e _ (by simpa using ht) hi).1.contDiffAt
  intro j hj
  by_cases heq : j=k
  · subst j
    simp only [ite_true]
    exact compact_family_prefactor_scaled_limit hQ A
      (fun eta=>paritySeries e b (fun u=>B (u,eta)) (fun u=>S (u,eta))) L k a hA hL (hF k)
      (by simpa only [ite_true] using hlimits k le_rfl)
      (fun i hi=>by simpa only [ne_of_lt hi,ite_false] using hlimits i hi.le)
  · simp only [heq,ite_false]
    exact compact_family_prefactor_lower_scaled_limit hQ A
      (fun eta=>paritySeries e b (fun u=>B (u,eta)) (fun u=>S (u,eta))) j a hA (hF j)
      (fun i hi=>by
        have hik : i<k := lt_of_le_of_lt hi (lt_of_le_of_ne hj heq)
        simpa only [ne_of_lt hik,ite_false] using hlimits i hik.le)

end
end IsingBulk.Joint.RegularEdges
