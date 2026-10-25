import IsingBulk.Anisotropic.RegularEdges.PhaseProducts

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Taylor's theorem transfers a proved quadratic input limit through an actual analytic germ. -/
theorem filtered_analytic_scaled_increment_limit {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0)
    {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {H : α→ℂ} {a : ℂ} (hH : Tendsto H l (𝓝 0))
    (hQ : Tendsto (fun t : α => H t/(τ t:ℂ)^2) l (𝓝 a)) :
    Tendsto (fun t : α => (f (H t)-f 0)/(τ t:ℂ)^2) l (𝓝 (deriv f 0*a)) := by
  obtain ⟨g,hg,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 2
  have hpoly (z : ℂ) :
      (∑ i∈Finset.range 2, (z^i/(i.factorial:ℂ)) • iteratedDeriv i f 0)=f 0+z*deriv f 0 := by
    simp [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one]
  have ht : Tendsto (fun t => (deriv f 0+H t*g (H t))*(H t/(τ t:ℂ)^2))
      l (𝓝 (deriv f 0*a)) := by
    simpa only [Function.comp_apply,zero_mul,add_zero] using! ((hH.mul (hg.continuousAt.tendsto.comp hH)).const_add (deriv f 0)).mul hQ
  apply ht.congr'
  filter_upwards [hH.eventually he,hτ.eventually self_mem_nhdsWithin] with t ht ht0
  rw [ht,hpoly]
  have htne : (τ t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<τ t from ht0).ne'
  simp only [smul_eq_mul]
  field_simp
  ring


def filteredEdgeIncrement {α : Type*} (τ : α → ℝ) (V : α → ℂ) (q : ℝ) (t : α) : ℂ :=
  Complex.I*(τ t:ℂ)^2+V t*(1-Complex.cos ((τ t:ℂ)*(q:ℂ)))

theorem filteredEdgeIncrement_tendsto {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {V : α → ℂ} {β : ℂ} (hV : Tendsto V l (𝓝 β)) (q : ℝ) :
    Tendsto (filteredEdgeIncrement τ V q) l (𝓝 0) := by
  have hz : Tendsto (fun t : α => (τ t:ℂ)) l (𝓝 0) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hτ.mono_right nhdsWithin_le_nhds)
  have hu : Tendsto (fun t : α => Complex.I*(τ t:ℂ)^2) l (𝓝 0) := by
    simpa using! (hz.pow 2).const_mul Complex.I
  have hcos : Tendsto (fun t : α => Complex.cos ((τ t:ℂ)*(q:ℂ))) l (𝓝 1) := by
    simpa using! Complex.continuous_cos.continuousAt.tendsto.comp (hz.mul_const (q:ℂ))
  simpa only [filteredEdgeIncrement,Function.comp_apply,sub_self,mul_zero,add_zero,zero_add] using!
    hu.add (hV.mul (hcos.const_sub (1:ℂ)))

theorem filteredEdgeIncrement_quotient_limit {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {V : α → ℂ} {β : ℂ} (hV : Tendsto V l (𝓝 β)) (q : ℝ) :
    Tendsto (fun t : α => filteredEdgeIncrement τ V q t/(τ t:ℂ)^2) l
      (𝓝 (Complex.I+β*(q:ℂ)^2/2)) := by
  have ht := (hV.mul ((angular_cosine_quadratic_limit q).comp hτ)).const_add Complex.I
  have ht' : Tendsto (fun t : α => Complex.I+V t*
      ((1-Complex.cos ((τ t:ℂ)*(q:ℂ)))/(τ t:ℂ)^2)) l
      (𝓝 (Complex.I+β*(q:ℂ)^2/2)) := by simpa only [Function.comp_apply,mul_div_assoc] using! ht
  apply ht'.congr'
  filter_upwards [hτ.eventually self_mem_nhdsWithin] with t ht
  have htne : (τ t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<τ t from ht).ne'
  unfold filteredEdgeIncrement
  field_simp

theorem filtered_root_scaled_increment_limit {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {V : α → ℂ} {β : ℂ} (hV : Tendsto V l (𝓝 β))
    {b : ℝ} (hb : |b|<1) (q : ℝ) :
    Tendsto (fun t : α => (continuedRoot ((b:ℂ)+filteredEdgeIncrement τ V q t)-
      continuedRoot (b:ℂ))/(τ t:ℂ)^2) l
      (𝓝 ((Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ))*
        (Complex.I+β*(q:ℂ)^2/2))) := by
  have ha : AnalyticAt ℂ (fun w => continuedRoot ((b:ℂ)+w)) 0 := by
    have hh : AnalyticAt ℂ continuedRoot ((b:ℂ)+0) := by
      simpa using continuedRoot_analyticAt (show (b:ℂ)∈continuedRootDomain from Or.inr (by simpa using hb))
    simpa using! hh.comp (f := fun w : ℂ => (b:ℂ)+w) (analyticAt_const.add analyticAt_id)
  have hd : deriv (fun w => continuedRoot ((b:ℂ)+w)) 0=
      Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ) := by
    have hh := (edgeParamRoot_parameter_hasDerivAt hb (fun _ => 0)).deriv
    simpa only [edgeParamRoot,edgeParamW,Real.cos_zero,Complex.ofReal_one,sub_self,mul_zero,add_zero] using hh
  have ht := filtered_analytic_scaled_increment_limit ha hτ
    (filteredEdgeIncrement_tendsto hτ hV q) (filteredEdgeIncrement_quotient_limit hτ hV q)
  simpa only [hd,add_zero] using ht

theorem filtered_root_tendsto {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {V : α → ℂ} {β : ℂ} (hV : Tendsto V l (𝓝 β))
    {b : ℝ} (hb : |b|<1) (q : ℝ) :
    Tendsto (fun t : α => continuedRoot ((b:ℂ)+filteredEdgeIncrement τ V q t)) l
      (𝓝 (continuedRoot (b:ℂ))) := by
  have hh := (continuedRoot_analyticAt (show (b:ℂ)∈continuedRootDomain from
    Or.inr (by simpa using hb))).continuousAt.tendsto
  exact hh.comp (by simpa using! (filteredEdgeIncrement_tendsto hτ hV q).const_add (b:ℂ))

theorem filtered_product_increment_limit {α : Type*} {l : Filter α} {τ : α → ℝ}
    (hτ : Tendsto τ l (𝓝[>] 0)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f : α→ι→ℂ} {d : ι→ℂ} {ζ : ℂ} (hζ : ζ≠0)
    (hf : ∀ i∈s, Tendsto (fun t => f t i) l (𝓝 ζ))
    (hd : ∀ i∈s, Tendsto (fun t : α => (f t i-ζ)/(τ t:ℂ)^2) l (𝓝 (d i))) :
    Tendsto (fun t : α => ((∏ i∈s, f t i)-ζ^s.card)/(τ t:ℂ)^2)
      l (𝓝 (ζ^s.card*∑ i∈s, d i/ζ)) := by
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℂ)) l (𝓝 0))
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hp : Tendsto (fun t => ∏ i∈s, f t i) l (𝓝 (ζ^s.card)) := by
      simpa using tendsto_finsetProd s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ht := ((hd a (Finset.mem_insert_self a s)).mul hp).add (hs.const_mul ζ)
    have he : d a*ζ^s.card+ζ*(ζ^s.card*∑ i∈s,d i/ζ)=
        ζ^(insert a s).card*∑ i∈insert a s,d i/ζ := by
      rw [Finset.card_insert_of_notMem ha,Finset.sum_insert ha,pow_succ]
      field_simp
    rw [he] at ht
    apply ht.congr'
    filter_upwards [hτ.eventually self_mem_nhdsWithin] with t ht0
    have htne : (τ t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<τ t from ht0).ne'
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,pow_succ]
    field_simp
    ring



/-- Quadratic resonant denominator asymptotics allow the anisotropy itself to
vary along the limiting filter; no fixed-parameter reduction is used. -/
theorem filtered_root_product_denominator_limit {α : Type*} {l : Filter α}
    {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {V : α → ℂ} {β : ℂ}
    (hV : Tendsto V l (𝓝 β)) {N : ℕ} {b : ℝ} (hb : |b|<1)
    (q : Fin N→ℝ) (hres : continuedRoot (b:ℂ)^N=1) :
    Tendsto (fun t : α => (1-∏ i, continuedRoot ((b:ℂ)+filteredEdgeIncrement τ V (q i) t))/(τ t:ℂ)^2)
      l (𝓝 ((N:ℂ)/(Real.sqrt (1-b^2):ℂ)-
        Complex.I*β/(2*(Real.sqrt (1-b^2):ℂ))*∑ i,(q i:ℂ)^2)) := by
  let ζ := continuedRoot (b:ℂ)
  let s : ℂ := (Real.sqrt (1-b^2):ℂ)
  have hζ : ζ≠0 := continuedRoot_nonzero _
  have hb' := abs_lt.mp hb
  have hs : s≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have ht := filtered_product_increment_limit hτ Finset.univ hζ
    (fun i _ => filtered_root_tendsto hτ hV hb (q i))
    (fun i _ => filtered_root_scaled_increment_limit hτ hV hb (q i))
  have hratio (i : Fin N) : (Complex.I*ζ/s*(Complex.I+β*(q i:ℂ)^2/2))/ζ=
      Complex.I/s*(Complex.I+β*(q i:ℂ)^2/2) := by field_simp
  have hterm (i : Fin N) : (Complex.I*ζ/s*(Complex.I+β*(q i:ℂ)^2/2))/ζ=
      -1/s+(Complex.I*β/(2*s))*(q i:ℂ)^2 := by
    rw [hratio]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hcoef : -(ζ^N*∑ i : Fin N,(Complex.I*ζ/s*(Complex.I+β*(q i:ℂ)^2/2))/ζ)=
      (N:ℂ)/s-Complex.I*β/(2*s)*∑ i,(q i:ℂ)^2 := by
    rw [hres,one_mul]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have ht' := ht.neg
  simp only [Finset.card_univ,Fintype.card_fin] at ht'
  change Tendsto (fun t : α => -(((∏ i,continuedRoot ((b:ℂ)+filteredEdgeIncrement τ V (q i) t))-ζ^N)/(τ t:ℂ)^2))
    l (𝓝 (-(ζ^N*∑ i : Fin N,(Complex.I*ζ/s*(Complex.I+β*(q i:ℂ)^2/2))/ζ))) at ht'
  rw [hcoef] at ht'
  apply ht'.congr'
  filter_upwards [] with t
  rw [hres]
  ring

end
end IsingBulk.Joint.RegularEdges
