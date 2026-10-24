import IsingBulk.Anisotropic.RegularEdges.EdgePairs

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Schur Set Filter
open scoped Topology

def edgeCircleCanceledKernel (b : ℝ) (B : ℂ → ℂ) (u y w : ℂ) : ℂ :=
  B u*canceledPair y w (edgeCircleRoot b B u y) (edgeCircleRoot b B u w)
def radialEdgePairProduct (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (r : ℝ) (qs : List ℝ) : ℂ :=
  IsingBulk.Schur.pairProduct (edgeCircleCanceledKernel b B u) (qs.map (radialEdgeY r))

theorem radialEdgeY_norm {r : ℝ} (hr : 0≤r) (q : ℝ) : ‖radialEdgeY r q‖=r := by
  simp [radialEdgeY,limitingAngle_norm,Real.norm_eq_abs,abs_of_nonneg hr]

private theorem root_kernel_norm_symm (b : ℝ) (B : ℂ → ℂ) (u a c : ℂ) :
    ‖pairKernel (edgeCircleRoot b B u a) (edgeCircleRoot b B u c)‖ =
      ‖pairKernel (edgeCircleRoot b B u c) (edgeCircleRoot b B u a)‖ := by
  have he : pairKernel (edgeCircleRoot b B u a) (edgeCircleRoot b B u c) =
      -pairKernel (edgeCircleRoot b B u c) (edgeCircleRoot b B u a) := by unfold pairKernel; ring
  rw [he,norm_neg]

theorem radial_complete_even_bound (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (R : ℝ)
    (hR : 0<R) (hR1 : R<1) (n : ℕ) (qs : List ℝ) (hlen : qs.length=2*n)
    {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (hd : ∀ q ∈ qs, ∀ t ∈ qs, 1-radialEdgeRoot b B (u,R) q*radialEdgeRoot b B (u,R) t≠0)
    (hK : ∀ q ∈ qs, ∀ t ∈ qs, ‖radialEdgePair b B (u,R) (q,t)‖≤r)
    (hP : ∀ q ∈ qs, ∀ t ∈ qs, ‖radialEdgeCanceledPair b B (u,R) (q,t)‖≤C) :
    ‖radialEdgePairProduct b B u R qs‖ ≤ (matchingCount n:ℝ)*C^n*r^(2*n*(n-1)) := by
  let K := fun a c => pairKernel (edgeCircleRoot b B u a) (edgeCircleRoot b B u c)
  have hy (q : ℝ) : ‖radialEdgeY R q‖<1 := by rw [radialEdgeY_norm hR.le]; exact hR1
  apply even_complete_pair_bound K (edgeCircleCanceledKernel b B u)
    (root_kernel_norm_symm b B u) n (qs.map (radialEdgeY R)) (by simpa using hlen) hr hC
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact denominator_ne_zero (hy q) (hy t)
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact hK q hq t ht
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact hP q hq t ht
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact edgeCircleRoot_pair_cancellation b B u
      (norm_ne_zero_iff.mp ((radialEdgeY_norm hR.le q).trans_ne hR.ne'))
      (norm_ne_zero_iff.mp ((radialEdgeY_norm hR.le t).trans_ne hR.ne'))
      (denominator_ne_zero (hy q) (hy t)) (hd q hq t ht)

theorem radial_complete_odd_bound (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (R : ℝ)
    (hR : 0<R) (hR1 : R<1) (n : ℕ) (qs : List ℝ) (hlen : qs.length=2*n+1)
    {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (hd : ∀ q ∈ qs, ∀ t ∈ qs, 1-radialEdgeRoot b B (u,R) q*radialEdgeRoot b B (u,R) t≠0)
    (hK : ∀ q ∈ qs, ∀ t ∈ qs, ‖radialEdgePair b B (u,R) (q,t)‖≤r)
    (hP : ∀ q ∈ qs, ∀ t ∈ qs, ‖radialEdgeCanceledPair b B (u,R) (q,t)‖≤C) :
    ‖radialEdgePairProduct b B u R qs‖ ≤ (matchingCount (n+1):ℝ)*C^n*r^(2*n*n) := by
  let K := fun a c => pairKernel (edgeCircleRoot b B u a) (edgeCircleRoot b B u c)
  have hy (q : ℝ) : ‖radialEdgeY R q‖<1 := by rw [radialEdgeY_norm hR.le]; exact hR1
  apply odd_complete_pair_bound K (edgeCircleCanceledKernel b B u)
    (root_kernel_norm_symm b B u) n (qs.map (radialEdgeY R)) (by simpa using hlen) hr hC
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact denominator_ne_zero (hy q) (hy t)
  · intro a ha he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    have hh := hy q
    rw [he,norm_neg,norm_one] at hh
    exact lt_irrefl _ hh
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact hK q hq t ht
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact hP q hq t ht
  · intro a ha c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact edgeCircleRoot_pair_cancellation b B u
      (norm_ne_zero_iff.mp ((radialEdgeY_norm hR.le q).trans_ne hR.ne'))
      (norm_ne_zero_iff.mp ((radialEdgeY_norm hR.le t).trans_ne hR.ne'))
      (denominator_ne_zero (hy q) (hy t)) (hd q hq t ht)

theorem radialEdgePairProduct_continuousAt_one (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (qs : List ℝ)
    (hdom : ∀ q ∈ qs, edgeParamW b B u q ∈ continuedRootDomain)
    (hd : ∀ q ∈ qs, ∀ t ∈ qs,
      1-radialEdgeRoot b B (u,1) q*radialEdgeRoot b B (u,1) t≠0) :
    ContinuousAt (fun R => radialEdgePairProduct b B u R qs) 1 := by
  have hy (q : ℝ) : ContinuousAt (fun R : ℝ => radialEdgeY R q) 1 := by
    unfold radialEdgeY
    fun_prop
  have hy0 (q : ℝ) : radialEdgeY 1 q≠0 := by
    rw [radialEdgeY_one]
    exact Complex.exp_ne_zero _
  have hroot (q : ℝ) (hq : q ∈ qs) :
      ContinuousAt (fun R : ℝ => edgeCircleRoot b B u (radialEdgeY R q)) 1 := by
    have hw : ContinuousAt (fun R : ℝ => edgeCircleW b B u (radialEdgeY R q)) 1 :=
      continuousAt_const.add (continuousAt_const.mul
        (continuousAt_const.sub (((hy q).add ((hy q).inv₀ (hy0 q))).div_const 2)))
    exact (continuedRoot_analyticAt (show edgeCircleW b B u (radialEdgeY 1 q) ∈ continuedRootDomain by
      simpa using hdom q hq)).continuousAt.comp
      (f := fun R : ℝ => edgeCircleW b B u (radialEdgeY R q)) hw
  have hh := continuousAt_pairProduct (edgeCircleCanceledKernel b B u)
    (qs.map (fun q R => radialEdgeY R q)) (1:ℝ) (by
      intro f hf g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      exact continuousAt_const.mul (continuousAt_canceledPair _ _ _ _ 1 (hy q) (hy t)
        (hroot q hq) (hroot t ht) (hy0 q) (hy0 t) (hd q hq t ht)))
  simpa only [List.map_map,Function.comp_def,radialEdgePairProduct] using hh

/-- Actual complete canceled-pair products at every angle configuration,
including reciprocal and coincident configurations, have the matched Gaussian
bound uniformly for all particle numbers in one complex parameter neighborhood. -/
theorem complete_edge_pairs_uniform {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ r C : ℝ, 0<r ∧ r<1 ∧ 0<C ∧ ∀ᶠ u in 𝓝 (0:ℂ),
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b B u 1 qs‖ ≤ (matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) ∧
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n+1 →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b B u 1 qs‖ ≤ (matchingCount (n+1):ℝ)*C^n*r^(2*n*n)) := by
  obtain ⟨r,hr,hr1,hKr⟩ := radialEdgePair_uniform hb hB hc
  obtain ⟨C,hC,hPC⟩ := radialEdgeCanceledPair_uniform hb hB hc
  have hden := radialEdgeRoot_denominator_uniform hb hB hc
  have hjoint : ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)),
      (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        1-radialEdgeRoot b B p q*radialEdgeRoot b B p t≠0) ∧
      (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖radialEdgePair b B p (q,t)‖≤r) ∧
      (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖radialEdgeCanceledPair b B p (q,t)‖≤C) := by
    filter_upwards [hden,hKr,hPC] with p hd hk hp
    exact ⟨hd,hk,hp⟩
  rw [nhds_prod_eq] at hjoint
  obtain ⟨pa,hpa,pR,hpR,hrect⟩ := Filter.eventually_prod_iff.mp hjoint
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [hpa,edgeParamW_uniform_domain hb hB hc] with u hu hdom
  have hunit := hrect hu (mem_of_mem_nhds hpR)
  have pass (qs : List ℝ) (hqs : ∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) (M : ℝ)
      (hm : ∀ R : ℝ, 0<R → R<1 → pR R → ‖radialEdgePairProduct b B u R qs‖≤M) :
      ‖radialEdgePairProduct b B u 1 qs‖≤M := by
    have hct := radialEdgePairProduct_continuousAt_one b B u qs
      (fun q hq => hdom q (hqs q hq))
      (fun q hq t ht => hunit.1 q (hqs q hq) t (hqs t ht))
    apply le_of_tendsto (hct.norm.mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    filter_upwards [hpR.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with R hR hR0 hR1
    exact hm R hR0 hR1 hR
  constructor
  · intro n qs hlen hqs
    apply pass qs hqs
    intro R hR hR1 hp
    have hh := hrect hu hp
    exact radial_complete_even_bound b B u R hR hR1 n qs hlen hr.le hC.le
      (fun q hq t ht => hh.1 q (hqs q hq) t (hqs t ht))
      (fun q hq t ht => hh.2.1 q (hqs q hq) t (hqs t ht))
      (fun q hq t ht => hh.2.2 q (hqs q hq) t (hqs t ht))
  · intro n qs hlen hqs
    apply pass qs hqs
    intro R hR hR1 hp
    have hh := hrect hu hp
    exact radial_complete_odd_bound b B u R hR hR1 n qs hlen hr.le hC.le
      (fun q hq t ht => hh.1 q (hqs q hq) t (hqs t ht))
      (fun q hq t ht => hh.2.1 q (hqs q hq) t (hqs t ht))
      (fun q hq t ht => hh.2.2 q (hqs q hq) t (hqs t ht))
end
end IsingBulk.Anisotropic.RegularEdges
