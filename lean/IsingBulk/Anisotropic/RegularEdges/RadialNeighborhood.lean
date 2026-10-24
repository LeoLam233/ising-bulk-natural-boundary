import IsingBulk.Anisotropic.RegularEdges.EdgeNeighborhood

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology

def edgeCircleW (b : ℝ) (B : ℂ → ℂ) (u y : ℂ) : ℂ :=
  (b:ℂ)+u+B u*(1-(y+y⁻¹)/2)
def edgeCircleRoot (b : ℝ) (B : ℂ → ℂ) (u y : ℂ) : ℂ :=
  continuedRoot (edgeCircleW b B u y)
def radialEdgeY (r q : ℝ) : ℂ := (r:ℂ)*limitingAngle q
def radialEdgeRoot (b : ℝ) (B : ℂ → ℂ) (p : ℂ × ℝ) (q : ℝ) : ℂ :=
  edgeCircleRoot b B p.1 (radialEdgeY p.2 q)
def radialEdgePair (b : ℝ) (B : ℂ → ℂ) (p : ℂ × ℝ) (q : ℝ × ℝ) : ℂ :=
  pairKernel (radialEdgeRoot b B p q.1) (radialEdgeRoot b B p q.2)
def radialEdgeCanceledPair (b : ℝ) (B : ℂ → ℂ) (p : ℂ × ℝ) (q : ℝ × ℝ) : ℂ :=
  B p.1*canceledPair (radialEdgeY p.2 q.1) (radialEdgeY p.2 q.2)
    (radialEdgeRoot b B p q.1) (radialEdgeRoot b B p q.2)

@[simp] theorem radialEdgeY_one (q : ℝ) : radialEdgeY 1 q=limitingAngle q := by
  simp [radialEdgeY]
@[simp] theorem edgeCircleW_unit (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (q : ℝ) :
    edgeCircleW b B u (limitingAngle q)=edgeParamW b B u q := by
  unfold edgeCircleW edgeParamW
  rw [limitingAngle_trace]
  push_cast
  ring
@[simp] theorem radialEdgeRoot_base (b : ℝ) (B : ℂ → ℂ) (q : ℝ) :
    radialEdgeRoot b B (0,1) q=edgeRoot b (B 0) q := by
  simp [radialEdgeRoot,edgeCircleRoot,edgeRoot]

theorem radialEdgeRoot_continuousAt_base {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (q : ℝ) :
    ContinuousAt (fun x : (ℂ × ℝ) × ℝ => radialEdgeRoot b B x.1 x.2) ((0,1),q) := by
  have hy : ContinuousAt (fun x : (ℂ × ℝ) × ℝ => radialEdgeY x.1.2 x.2) ((0,1),q) := by
    unfold radialEdgeY limitingAngle
    fun_prop
  have hzero : radialEdgeY 1 q≠0 := by
    rw [radialEdgeY_one]
    exact Complex.exp_ne_zero _
  have hw : ContinuousAt (fun x : (ℂ × ℝ) × ℝ =>
      edgeCircleW b B x.1.1 (radialEdgeY x.1.2 x.2)) ((0,1),q) := by
    unfold edgeCircleW
    exact (continuousAt_const.add (continuousAt_fst.comp continuousAt_fst)).add
      ((hc.comp (f := fun x : (ℂ × ℝ) × ℝ => x.1.1) (x := ((0,1),q))
        (continuousAt_fst.comp continuousAt_fst)).mul
        (continuousAt_const.sub ((hy.add (hy.inv₀ hzero)).div_const 2)))
  have hdom : edgeCircleW b B 0 (radialEdgeY 1 q) ∈ continuedRootDomain := by
    simpa using edgeW_domain hb hB q
  exact (continuedRoot_analyticAt hdom).continuousAt.comp
    (f := fun x : (ℂ × ℝ) × ℝ => edgeCircleW b B x.1.1 (radialEdgeY x.1.2 x.2)) hw

private theorem radial_roots_pair_continuous {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (q : ℝ × ℝ) :
    ContinuousAt (fun x : (ℂ × ℝ) × (ℝ × ℝ) => radialEdgeRoot b B x.1 x.2.1) ((0,1),q) ∧
    ContinuousAt (fun x : (ℂ × ℝ) × (ℝ × ℝ) => radialEdgeRoot b B x.1 x.2.2) ((0,1),q) := by
  constructor
  · exact (radialEdgeRoot_continuousAt_base hb hB hc q.1).comp
      (x := ((0,1),q)) (f := fun x : (ℂ × ℝ) × (ℝ × ℝ) => (x.1,x.2.1))
      (continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd))
  · exact (radialEdgeRoot_continuousAt_base hb hB hc q.2).comp
      (x := ((0,1),q)) (f := fun x : (ℂ × ℝ) × (ℝ × ℝ) => (x.1,x.2.2))
      (continuousAt_fst.prodMk (continuousAt_snd.comp continuousAt_snd))

theorem radialEdgePair_continuousAt_base {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (q : ℝ × ℝ) :
    ContinuousAt (fun x : (ℂ × ℝ) × (ℝ × ℝ) => radialEdgePair b B x.1 x.2) ((0,1),q) := by
  obtain ⟨h₁,h₂⟩ := radial_roots_pair_continuous hb hB hc q
  exact (h₁.sub h₂).div (continuousAt_const.sub (h₁.mul h₂))
    (by simpa using edgeRoot_pair_denominator_ne_zero hb hB q.1 q.2)

theorem radialEdgeCanceledPair_continuousAt_base {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (q : ℝ × ℝ) :
    ContinuousAt (fun x : (ℂ × ℝ) × (ℝ × ℝ) => radialEdgeCanceledPair b B x.1 x.2) ((0,1),q) := by
  obtain ⟨h₁,h₂⟩ := radial_roots_pair_continuous hb hB hc q
  unfold radialEdgeCanceledPair
  apply (hc.comp (x := ((0,1),q)) (f := fun x : (ℂ × ℝ) × (ℝ × ℝ) => x.1.1)
    (continuousAt_fst.comp continuousAt_fst)).mul
  apply continuousAt_canceledPair _ _ _ _ ((0,1),q)
    (by unfold radialEdgeY limitingAngle; fun_prop)
    (by unfold radialEdgeY limitingAngle; fun_prop) h₁ h₂
  · simpa only [radialEdgeY_one,limitingAngle] using Complex.exp_ne_zero ((q.1:ℂ)*Complex.I)
  · simpa only [radialEdgeY_one,limitingAngle] using Complex.exp_ne_zero ((q.2:ℂ)*Complex.I)
  · simpa using edgeRoot_pair_denominator_ne_zero hb hB q.1 q.2

theorem radialEdgePair_uniform {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ r : ℝ, 0<r ∧ r<1 ∧ ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)),
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖radialEdgePair b B p (q,t)‖ ≤ r := by
  obtain ⟨r,hr,hr1,hm⟩ := edgeRoot_uniform_schur hb hB
  refine ⟨(r+1)/2,by positivity,by linarith,?_⟩
  have he : ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)), ∀ q ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi,
      ‖radialEdgePair b B p q‖ < (r+1)/2 := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro q hq
    apply (radialEdgePair_continuousAt_base hb hB hc q).norm.eventually_lt continuousAt_const
    have hh := hm q.1 hq.1 q.2 hq.2
    simp only [radialEdgePair,radialEdgeRoot_base]
    linarith
  filter_upwards [he] with p hp q hq t ht
  exact (hp (q,t) ⟨hq,ht⟩).le

theorem radialEdgeCanceledPair_uniform {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)),
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖radialEdgeCanceledPair b B p (q,t)‖ ≤ C := by
  let K : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (radialEdgeCanceledPair b B (0,1)) K := by
    intro q _
    exact ((radialEdgeCanceledPair_continuousAt_base hb hB hc q).comp
      (f := fun q : ℝ × ℝ => (((0:ℂ),(1:ℝ)),q))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcont
  let C := max M 0+1
  refine ⟨C,by dsimp [C]; linarith [le_max_right M 0],?_⟩
  have he : ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)), ∀ q ∈ K, ‖radialEdgeCanceledPair b B p q‖ < C := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    apply (radialEdgeCanceledPair_continuousAt_base hb hB hc q).norm.eventually_lt continuousAt_const
    exact (hM q hq).trans_lt (by dsimp [C]; linarith [le_max_left M 0])
  filter_upwards [he] with p hp q hq t ht
  exact (hp (q,t) ⟨hq,ht⟩).le

theorem radialEdgeRoot_denominator_uniform {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)),
      ∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
        1-radialEdgeRoot b B p q*radialEdgeRoot b B p t≠0 := by
  have he : ∀ᶠ p in 𝓝 ((0:ℂ),(1:ℝ)), ∀ q ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi,
      1-radialEdgeRoot b B p q.1*radialEdgeRoot b B p q.2≠0 := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro q _
    obtain ⟨h₁,h₂⟩ := radial_roots_pair_continuous hb hB hc q
    exact (continuousAt_const.sub (h₁.mul h₂)).eventually_ne
      (by simpa using edgeRoot_pair_denominator_ne_zero hb hB q.1 q.2)
  filter_upwards [he] with p hp q hq t ht
  exact hp (q,t) ⟨hq,ht⟩
end
end IsingBulk.Anisotropic.RegularEdges
