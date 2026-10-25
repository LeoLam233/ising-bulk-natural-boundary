import IsingBulk.Joint.RegularEdges.ComplexPolydisk
import IsingBulk.Anisotropic.RegularEdges.FullPairBound

/-! # Common all-particle Gaussian bounds
The constants are chosen on independent complex parameter neighborhoods, before
choosing the particle number. Radial regularization is used only to prove the
bound, so reciprocal angle coincidences are included in the conclusion.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Schur
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

theorem compact_denominator_disk {b : ℝ} {K : Set ℂ}
    (hb : |b| < 1) (hK : IsCompact K) (hB : ∀ B ∈ K, 0 < B.im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u B : ℂ, ‖u‖ < δ → B ∈ K →
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        1 - root b (u,B) q * root b (u,B) t ≠ 0 := by
  let L : Set (ℂ × (ℝ × ℝ)) := K ×ˢ (Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi)
  have he : ∀ᶠ u : ℂ in 𝓝 0, ∀ x ∈ L,
      1 - root b (u,x.1) x.2.1 * root b (u,x.1) x.2.2 ≠ 0 := by
    apply (hK.prod (isCompact_Icc.prod isCompact_Icc)).eventually_forall_of_forall_eventually
    intro x hx
    have h₁ := (root_continuousAt (show dispersion b (0,x.1) x.2.1 ∈ continuedRootDomain by
      simpa using edgeW_domain hb (hB x.1 hx.1) x.2.1)).comp
      (x := ((0:ℂ),x))
      (f := fun y : ℂ × (ℂ × (ℝ × ℝ)) => ((y.1,y.2.1),y.2.2.1)) (by fun_prop)
    have h₂ := (root_continuousAt (show dispersion b (0,x.1) x.2.2 ∈ continuedRootDomain by
      simpa using edgeW_domain hb (hB x.1 hx.1) x.2.2)).comp
      (x := ((0:ℂ),x))
      (f := fun y : ℂ × (ℂ × (ℝ × ℝ)) => ((y.1,y.2.1),y.2.2.2)) (by fun_prop)
    exact (continuousAt_const.sub (h₁.mul h₂)).eventually_ne
      (by simpa using edgeRoot_pair_denominator_ne_zero hb (hB x.1 hx.1) x.2.1 x.2.2)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨δ,hδ,fun u B hu hBK q hq t ht =>
    hδb (show u ∈ ball (0:ℂ) δ by simpa using hu) (B,(q,t)) ⟨hBK,hq,ht⟩⟩

private theorem radial_root_continuousAt_one {b : ℝ} {u B : ℂ} {q : ℝ}
    (hd : dispersion b (u,B) q ∈ continuedRootDomain) :
    ContinuousAt (fun x : ℝ × ℝ => radialEdgeRoot b (fun _ => B) (u,x.1) x.2) (1,q) := by
  have hy : ContinuousAt (fun x : ℝ × ℝ => radialEdgeY x.1 x.2) (1,q) := by
    unfold radialEdgeY limitingAngle
    fun_prop
  have hy0 : radialEdgeY 1 q ≠ 0 := by simp [limitingAngle,Complex.exp_ne_zero]
  have hw : ContinuousAt (fun x : ℝ × ℝ => edgeCircleW b (fun _ => B) u
      (radialEdgeY x.1 x.2)) (1,q) :=
    continuousAt_const.add (continuousAt_const.mul
      (continuousAt_const.sub ((hy.add (hy.inv₀ hy0)).div_const 2)))
  have hd' : edgeCircleW b (fun _ => B) u (radialEdgeY 1 q) ∈ continuedRootDomain := by
    simpa only [radialEdgeY_one,edgeCircleW_unit,edgeParamW,dispersion] using hd
  change ContinuousAt (fun x : ℝ × ℝ => continuedRoot
    (edgeCircleW b (fun _ => B) u (radialEdgeY x.1 x.2))) (1,q)
  exact (continuedRoot_analyticAt hd').continuousAt.comp (x := (1,q))
    (f := fun x : ℝ × ℝ => edgeCircleW b (fun _ => B) u (radialEdgeY x.1 x.2)) hw


private theorem radial_pair_continuousAt_one {b : ℝ} {u B : ℂ} {q : ℝ × ℝ}
    (h₁ : dispersion b (u,B) q.1 ∈ continuedRootDomain)
    (h₂ : dispersion b (u,B) q.2 ∈ continuedRootDomain)
    (hd : 1-root b (u,B) q.1*root b (u,B) q.2 ≠ 0) :
    ContinuousAt (fun x : ℝ × (ℝ × ℝ) => radialEdgePair b (fun _ => B) (u,x.1) x.2) (1,q) ∧
    ContinuousAt (fun x : ℝ × (ℝ × ℝ) => radialEdgeCanceledPair b (fun _ => B) (u,x.1) x.2) (1,q) ∧
    ContinuousAt (fun x : ℝ × (ℝ × ℝ) => 1-
      radialEdgeRoot b (fun _ => B) (u,x.1) x.2.1*
      radialEdgeRoot b (fun _ => B) (u,x.1) x.2.2) (1,q) := by
  have ha := (radial_root_continuousAt_one h₁).comp (x := (1,q))
    (f := fun x : ℝ × (ℝ × ℝ) => (x.1,x.2.1)) (by fun_prop)
  have hc := (radial_root_continuousAt_one h₂).comp (x := (1,q))
    (f := fun x : ℝ × (ℝ × ℝ) => (x.1,x.2.2)) (by fun_prop)
  have hd' : 1-radialEdgeRoot b (fun _ => B) (u,1) q.1*
      radialEdgeRoot b (fun _ => B) (u,1) q.2 ≠ 0 := by
    simpa [radialEdgeRoot,edgeCircleRoot,edgeParamW,root,dispersion] using hd
  refine ⟨(ha.sub hc).div (continuousAt_const.sub (ha.mul hc)) hd',?_,
    continuousAt_const.sub (ha.mul hc)⟩
  apply continuousAt_const.mul
  apply continuousAt_canceledPair _ _ _ _ (1,q)
    (by unfold radialEdgeY limitingAngle; fun_prop)
    (by unfold radialEdgeY limitingAngle; fun_prop) ha hc
  · simp [limitingAngle,Complex.exp_ne_zero]
  · simp [limitingAngle,Complex.exp_ne_zero]
  · exact hd'

/-- Literal compact-angle bounds imply the matched all-particle bounds.
The slight enlargement of the constants is independent of the particle count. -/
theorem complete_pairs_of_angular_bounds {b : ℝ} {u B : ℂ} {r C : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 < C)
    (hdom : ∀ q ∈ Icc (-Real.pi) Real.pi, dispersion b (u,B) q ∈ continuedRootDomain)
    (hden : ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
      1-root b (u,B) q*root b (u,B) t ≠ 0)
    (hpair : ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
      ‖rootPair b (u,B) (q,t)‖ ≤ r ∧ ‖completePair b (u,B) (q,t)‖ ≤ C) :
    (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n →
      (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
      ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
        (matchingCount n:ℝ)*(C+1)^n*((r+1)/2)^(2*n*(n-1))) ∧
    (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n+1 →
      (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
      ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
        (matchingCount (n+1):ℝ)*(C+1)^n*((r+1)/2)^(2*n*n)) := by
  have he : ∀ᶠ R : ℝ in 𝓝 1, ∀ q ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi,
      (1-radialEdgeRoot b (fun _ => B) (u,R) q.1*
        radialEdgeRoot b (fun _ => B) (u,R) q.2 ≠ 0) ∧
      ‖radialEdgePair b (fun _ => B) (u,R) q‖ ≤ (r+1)/2 ∧
      ‖radialEdgeCanceledPair b (fun _ => B) (u,R) q‖ ≤ C+1 := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro q hq
    obtain ⟨hpk,hpc,hpd⟩ := radial_pair_continuousAt_one (hdom q.1 hq.1)
      (hdom q.2 hq.2) (hden q.1 hq.1 q.2 hq.2)
    have hk : ‖radialEdgePair b (fun _ => B) (u,1) q‖ < (r+1)/2 := by
      have hh := (hpair q.1 hq.1 q.2 hq.2).1
      simp only [radialEdgePair,radialEdgeRoot,edgeCircleRoot,radialEdgeY_one,
        edgeCircleW_unit,edgeParamW,rootPair,root,dispersion] at *
      linarith
    have hc : ‖radialEdgeCanceledPair b (fun _ => B) (u,1) q‖ < C+1 := by
      have hh := (hpair q.1 hq.1 q.2 hq.2).2
      simp only [radialEdgeCanceledPair,radialEdgeRoot,edgeCircleRoot,radialEdgeY_one,edgeCircleW_unit]
      simpa only [edgeParamW,completePair,root,dispersion,limitingAngle,mul_comm] using
        hh.trans_lt (lt_add_one C)
    have hd : 1-radialEdgeRoot b (fun _ => B) (u,1) q.1*
        radialEdgeRoot b (fun _ => B) (u,1) q.2 ≠ 0 := by
      simpa [radialEdgeRoot,edgeCircleRoot,edgeParamW,root,dispersion] using hden q.1 hq.1 q.2 hq.2
    filter_upwards [hpd.eventually_ne hd,hpk.norm.eventually_lt continuousAt_const hk,
      hpc.norm.eventually_lt continuousAt_const hc] with x hd hk hc
    exact ⟨hd,hk.le,hc.le⟩
  have pass (qs : List ℝ) (hqs : ∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) (M : ℝ)
      (hm : ∀ R : ℝ, 0<R → R<1 →
        (∀ q ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi,
          (1-radialEdgeRoot b (fun _ => B) (u,R) q.1*radialEdgeRoot b (fun _ => B) (u,R) q.2 ≠ 0) ∧
          ‖radialEdgePair b (fun _ => B) (u,R) q‖ ≤ (r+1)/2 ∧
          ‖radialEdgeCanceledPair b (fun _ => B) (u,R) q‖ ≤ C+1) →
        ‖radialEdgePairProduct b (fun _ => B) u R qs‖≤M) :
      ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖≤M := by
    have hc := radialEdgePairProduct_continuousAt_one b (fun _ => B) u qs
      (fun q hq => hdom q (hqs q hq)) (by
        intro q hq t ht
        simpa [radialEdgeRoot,edgeCircleRoot,edgeParamW,root,dispersion] using
          hden q (hqs q hq) t (hqs t ht))
    apply le_of_tendsto (hc.norm.mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with R hR hR0 hR1
    exact hm R hR0 hR1 hR
  constructor
  · intro n qs hlen hqs
    apply pass qs hqs
    intro R hR hR1 hh
    exact radial_complete_even_bound b (fun _ => B) u R hR hR1 n qs hlen
      (by positivity) (by positivity)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).1)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).2.1)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).2.2)
  · intro n qs hlen hqs
    apply pass qs hqs
    intro R hR hR1 hh
    exact radial_complete_odd_bound b (fun _ => B) u R hR hR1 n qs hlen
      (by positivity) (by positivity)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).1)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).2.1)
      (fun q hq t ht => (hh (q,t) ⟨hqs q hq,hqs t ht⟩).2.2)


/-- One normal disk and one Gaussian estimate for an arbitrary compact family
of genuinely complex anisotropies. The quantifier over all particle numbers is
inside the already fixed disk and constants. -/
theorem compact_complete_pairs {b : ℝ} {K : Set ℂ}
    (hb : |b| < 1) (hK : IsCompact K) (hB : ∀ B ∈ K, 0 < B.im) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ r < 1 ∧ 0 < C ∧
      ∀ u B : ℂ, ‖u‖ < δ → B ∈ K →
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
          (matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) ∧
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n+1 →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
          (matchingCount (n+1):ℝ)*C^n*r^(2*n*n)) := by
  obtain ⟨δ,r,C,hδ,hr,hr1,hC,hbound⟩ := compact_parameter_disk hb hK hB
  obtain ⟨ε,hε,hden⟩ := compact_denominator_disk hb hK hB
  refine ⟨min δ ε,(r+1)/2,C+1,lt_min hδ hε,by positivity,by linarith,by positivity,?_⟩
  intro u B hu hBK
  obtain ⟨hdom,hpair⟩ := hbound u B (hu.trans_le (min_le_left _ _)) hBK
  exact complete_pairs_of_angular_bounds hr hr1 hC hdom
    (hden u B (hu.trans_le (min_le_right _ _)) hBK) hpair

/-- The complete pair numerator has one common complex polydisk in independent
`u` and `B`, with the Schur Gaussian estimate valid for every particle number. -/
theorem independent_complete_pairs_polydisk {b : ℝ} {B₀ : ℂ}
    (hb : |b| < 1) (hB : 0 < B₀.im) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ r < 1 ∧ 0 < C ∧
      ∀ u B : ℂ, ‖u‖ < δ → ‖B-B₀‖ < δ →
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
          (matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) ∧
      (∀ n : ℕ, ∀ qs : List ℝ, qs.length=2*n+1 →
        (∀ q ∈ qs, q ∈ Icc (-Real.pi) Real.pi) →
        ‖radialEdgePairProduct b (fun _ => B) u 1 qs‖ ≤
          (matchingCount (n+1):ℝ)*C^n*r^(2*n*n)) := by
  obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp
    (Complex.continuous_im.continuousAt.eventually_const_lt hB)
  have hK (B : ℂ) (hBK : B ∈ closedBall B₀ (ε/2)) : 0 < B.im := by
    apply hεb
    exact mem_ball.mpr ((mem_closedBall.mp hBK).trans_lt (by linarith))
  obtain ⟨δ,r,C,hδ,hr,hr1,hC,hbound⟩ := compact_complete_pairs hb (isCompact_closedBall B₀ (ε/2)) hK
  refine ⟨min δ (ε/2),r,C,lt_min hδ (by positivity),hr,hr1,hC,?_⟩
  intro u B hu hBB
  apply hbound u B (hu.trans_le (min_le_left _ _))
  exact mem_closedBall.mpr (by
    rw [dist_eq_norm]
    exact (hBB.trans_le (min_le_right _ _)).le)

end
end IsingBulk.Joint.RegularEdges
