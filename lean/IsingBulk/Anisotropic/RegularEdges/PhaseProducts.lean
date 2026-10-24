import IsingBulk.Anisotropic.RegularEdges.PhaseScaling
import IsingBulk.Anisotropic.RegularEdges.LeadingCollision

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

theorem scaled_product_increment_limit {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f : ℝ→ι→ℂ} {d : ι→ℂ} {ζ : ℂ} (hζ : ζ≠0)
    (hf : ∀ i∈s, Tendsto (fun t => f t i) (𝓝[>] 0) (𝓝 ζ))
    (hd : ∀ i∈s, Tendsto (fun t : ℝ => (f t i-ζ)/(t:ℂ)^2) (𝓝[>] 0) (𝓝 (d i))) :
    Tendsto (fun t : ℝ => ((∏ i∈s, f t i)-ζ^s.card)/(t:ℂ)^2)
      (𝓝[>] 0) (𝓝 (ζ^s.card*∑ i∈s, d i/ζ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hp : Tendsto (fun t => ∏ i∈s, f t i) (𝓝[>] 0) (𝓝 (ζ^s.card)) := by
      simpa using tendsto_finsetProd s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ht := ((hd a (Finset.mem_insert_self a s)).mul hp).add (hs.const_mul ζ)
    have he : d a*ζ^s.card+ζ*(ζ^s.card*∑ i∈s,d i/ζ)=
        ζ^(insert a s).card*∑ i∈insert a s,d i/ζ := by
      rw [Finset.card_insert_of_notMem ha,Finset.sum_insert ha,pow_succ]
      field_simp
    rw [he] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have htne : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<t from ht0).ne'
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,pow_succ]
    field_simp
    ring

theorem edgeParamRoot_scaled_tendsto {b : ℝ} (hb : |b|<1) {B : ℂ→ℂ}
    (hB : ContinuousAt B 0) (q : ℝ) :
    Tendsto (fun t : ℝ => edgeParamRoot b B (Complex.I*(t:ℂ)^2) (t*q))
      (𝓝[>] 0) (𝓝 (continuedRoot (b:ℂ))) := by
  have hc := edgeParamRoot_continuousAt b hB
    (show edgeParamW b B 0 0∈continuedRootDomain by
      simp only [edgeParamW,Real.cos_zero,Complex.ofReal_one,sub_self,mul_zero,add_zero]
      exact Or.inr (by simpa using hb))
  have hct : Continuous (fun t : ℝ => (Complex.I*(t:ℂ)^2,t*q)) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (Complex.I*(t:ℂ)^2,t*q)) (𝓝[>] 0) (𝓝 ((0:ℂ),(0:ℝ))) := by
    simpa using! (hct.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [Function.comp_apply,edgeParamRoot,edgeParamW,Real.cos_zero,Complex.ofReal_one,
    sub_self,mul_zero,add_zero] using! hc.tendsto.comp ht

/-- The actual resonant lattice denominator has this anisotropic quadratic scaling limit. -/
theorem edgeRootProduct_scaled_denominator_limit {N : ℕ} {b : ℝ} (hb : |b|<1)
    {B : ℂ→ℂ} (hB : ContinuousAt B 0) (q : Fin N→ℝ)
    (hres : continuedRoot (b:ℂ)^N=1) :
    Tendsto (fun t : ℝ => (1-edgeRootProduct b B (Complex.I*(t:ℂ)^2) (fun i => t*q i))/(t:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((N:ℂ)/(Real.sqrt (1-b^2):ℂ)-
        Complex.I*B 0/(2*(Real.sqrt (1-b^2):ℂ))*∑ i,(q i:ℂ)^2)) := by
  let ζ := continuedRoot (b:ℂ)
  let s : ℂ := (Real.sqrt (1-b^2):ℂ)
  have hζ : ζ≠0 := continuedRoot_nonzero _
  have hb' := abs_lt.mp hb
  have hs : s≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have ht := scaled_product_increment_limit Finset.univ hζ
    (fun i _ => edgeParamRoot_scaled_tendsto hb hB (q i))
    (fun i _ => edgeParamRoot_scaled_increment_limit hb hB (q i))
  have hratio (i : Fin N) : (Complex.I*ζ/s*(Complex.I+B 0*(q i:ℂ)^2/2))/ζ=
      Complex.I/s*(Complex.I+B 0*(q i:ℂ)^2/2) := by field_simp
  have hterm (i : Fin N) : (Complex.I*ζ/s*(Complex.I+B 0*(q i:ℂ)^2/2))/ζ=
      -1/s+(Complex.I*B 0/(2*s))*(q i:ℂ)^2 := by
    rw [hratio]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hcoef : -(ζ^N*∑ i : Fin N,(Complex.I*ζ/s*(Complex.I+B 0*(q i:ℂ)^2/2))/ζ)=
      (N:ℂ)/s-Complex.I*B 0/(2*s)*∑ i,(q i:ℂ)^2 := by
    rw [hres,one_mul]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have ht' := ht.neg
  simp only [Finset.card_univ,Fintype.card_fin] at ht'
  change Tendsto (fun t : ℝ => -(((∏ i,edgeParamRoot b B (Complex.I*(t:ℂ)^2) (t*q i))-ζ^N)/(t:ℂ)^2))
    (𝓝[>] 0) (𝓝 (-(ζ^N*∑ i : Fin N,(Complex.I*ζ/s*(Complex.I+B 0*(q i:ℂ)^2/2))/ζ))) at ht'
  rw [hcoef] at ht'
  apply ht'.congr'
  filter_upwards [] with t
  dsimp [edgeRootProduct]
  rw [hres]
  ring

end
end IsingBulk.Anisotropic.RegularEdges
