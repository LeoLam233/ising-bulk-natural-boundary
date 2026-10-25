import IsingBulk.Joint.RegularEdges.FamilySeriesLimit
import IsingBulk.Joint.RegularEdges.FamilyLeadingFull
import IsingBulk.Joint.RegularEdges.FamilyLeadingLowerFull
import IsingBulk.Joint.RegularEdges.FamilyFiniteSums
import IsingBulk.Anisotropic.RegularEdges.LeadingArithmetic
import IsingBulk.Anisotropic.RegularEdges.PhasePrime

/-! # Uniform complete-parity asymptotics over genuine holomorphic families -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
  Set Filter Metric MeasureTheory
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem uniform_limit_of_common_radius {Q : Set E} {F : ℝ→E→ℂ} {g : E→ℂ}
    (h : ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ‖F t eta-g eta‖<ε) :
    TendstoUniformlyOn F g (𝓝[>] (0:ℝ)) Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := h ε hε
  filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with t ht htpos
  intro eta heta
  simpa only [dist_eq_norm,norm_sub_rev] using hbound eta heta t htpos ht

/-- Every derivative through the first singular order is treated at once.
The limit is nonzero exactly at that order. Finite lower and higher particles
and the infinite tail are all included in the actual parity series. -/
theorem compact_family_parity_derivative_uniform_limit {b : ℝ} (B S : ℂ × E→ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    {e p k a : ℕ} (ha : 0<a) (hp : p<k+2)
    (hres : continuedRoot (b:ℂ)^(2*p+e+1)=1)
    (hlower : ∀i<p,continuedRoot (b:ℂ)^(2*i+e+1)≠1)
    (hhigher : ∀ i : ℕ, p < i → 1 ≤ 2*i+e ∧ 2*(k+1) ≤ (2*i+e+1)*(2*i+e))
    (hbalance : (2*p+e)+a+(2*p+e+1)*(2*p+e)=2*(k+1))
    (hmajorant : Integrable (@shapeMajorant (2*p+e) k))
    (hperiod : ContinuousOn (shapePeriod (2*p+e) k ((2*p+e+1)/Real.sqrt (1-b^2)))
      {c : ℂ | 0<c.re}) (j : ℕ) (hj : j≤k) :
    TendstoUniformlyOn (fun (t : ℝ) eta=>(t^a) • iteratedDeriv j
      (paritySeries e b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2))
      (fun eta=>if j=k then edgeCoefficientLeading (2*p+e) k b
        (fun u=>B (u,eta)) (fun u=>S (u,eta)) else 0) (𝓝[>] (0:ℝ)) Q := by
  have htend : Tendsto (fun t : ℝ=>Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ=>Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hi : ∀t : ℝ,0<t → 0<(Complex.I*(t:ℂ)^2).im := by
    intro t ht
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    positivity
  obtain ⟨δ,hδ,hjets⟩ := compact_family_paritySeries_local_jets B S hb hQ hB hS hBi hS0
  obtain ⟨ρ,hρ,htails⟩ := compact_family_full_coefficient_tails B S hb hQ hB hS hBi hS0
  obtain ⟨G,hG,_,hbound⟩ := htails j
  apply uniform_scaled_series_first_limit ha hp
    (f := fun i t eta=>iteratedDeriv j
      (angularCoefficient (2*i+e) b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2))
  · filter_upwards [htend.eventually (ball_mem_nhds _ hδ),self_mem_nhdsWithin] with t ht htpos
    intro eta heta
    exact (hjets eta heta e _ (by simpa using ht) (hi t htpos)).2 j
  · intro i _
    by_cases hip : i=p
    · subst i
      simp only [ite_true]
      by_cases hjk : j=k
      · subst j
        simp only [ite_true]
        exact uniform_limit_of_common_radius
          (compact_family_fullCoefficient_uniform_limit ha hbalance hmajorant B S hb hQ hB hBi hS hS0 hres (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hperiod))
      · simp only [hjk,ite_false]
        apply uniform_limit_of_common_radius
        simpa only [sub_zero] using
          compact_family_lowerFullCoefficient_uniform_limit ha (lt_of_le_of_ne hj hjk)
            hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
    · simp only [hip,ite_false]
      rcases lt_or_gt_of_ne hip with hlt|hgt
      · obtain ⟨r,C,hr,_,hbnd⟩ := compact_family_nonresonant_coefficient_bound B S hb hQ hB hBi hS hS0 (hlower i hlt) j
        apply uniform_bounded_scaled_zero ha (D := C)
        filter_upwards [htend.eventually (ball_mem_nhds _ hr),self_mem_nhdsWithin] with t ht htpos
        intro eta heta
        exact hbnd eta heta _ (by simpa using ht) (hi t htpos)
      · obtain ⟨r,C,hr,_,hbnd⟩ := compact_family_higher_coefficient_bound (hhigher i hgt).1
          (show 2*(j+1)≤(2*i+e+1)*(2*i+e) by have hdeg := (hhigher i hgt).2; omega) B S hb hQ hB hBi hS hS0
        apply uniform_bounded_scaled_zero ha (D := C)
        filter_upwards [(eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htpos
        intro eta heta
        exact hbnd eta heta t htpos ht
  · exact hG.comp_injective (i := fun i : ℕ=>2*(k-j)+2*i+1+e) (by intro x y h; dsimp at h; omega)
  · filter_upwards [htend.eventually (ball_mem_nhds _ hρ),self_mem_nhdsWithin] with t ht htpos
    intro eta heta i
    have hh := hbound eta heta _ (by simpa using ht) (hi t htpos) (2*(k-j)+2*i+1+e)
    simpa only [Function.comp_def,show 2*j+3+(2*(k-j)+2*i+1+e)=2*(i+(k+2))+e by omega] using hh

end
end IsingBulk.Joint.RegularEdges
