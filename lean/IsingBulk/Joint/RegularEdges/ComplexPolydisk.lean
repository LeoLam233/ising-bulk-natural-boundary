import IsingBulk.Anisotropic.RegularEdges.EdgeNeighborhood

/-! # Independent complex regular-edge parameter neighborhoods

The parameter is the pair `(u,B)`, not a fixed-ratio temperature or a collection
of separately chosen one-dimensional disks.  The same root sheet, strict Schur
constant, and bound for the canceled pair hold on one complex product polydisk.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def dispersion (b : ℝ) (p : ℂ × ℂ) (q : ℝ) : ℂ :=
  (b : ℂ) + p.1 + p.2 * (1 - (Real.cos q : ℂ))

def root (b : ℝ) (p : ℂ × ℂ) (q : ℝ) : ℂ := continuedRoot (dispersion b p q)

def rootPair (b : ℝ) (p : ℂ × ℂ) (q : ℝ × ℝ) : ℂ :=
  pairKernel (root b p q.1) (root b p q.2)

def completePair (b : ℝ) (p : ℂ × ℂ) (q : ℝ × ℝ) : ℂ :=
  p.2 * canceledPair (Complex.exp (Complex.I*q.1)) (Complex.exp (Complex.I*q.2))
    (root b p q.1) (root b p q.2)

@[simp] theorem dispersion_zero (b : ℝ) (B : ℂ) (q : ℝ) :
    dispersion b (0,B) q = edgeW b B q := by simp [dispersion,edgeW]
@[simp] theorem root_zero (b : ℝ) (B : ℂ) (q : ℝ) :
    root b (0,B) q = edgeRoot b B q := by simp [root,edgeRoot]

/-- This is genuinely joint complex analyticity in the two independent
coordinates. -/
theorem dispersion_analyticAt (b : ℝ) (p : ℂ × ℂ) (q : ℝ) :
    AnalyticAt ℂ (fun x => dispersion b x q) p :=
  (analyticAt_const.add analyticAt_fst).add (analyticAt_snd.mul analyticAt_const)

theorem root_analyticAt {b : ℝ} {p : ℂ × ℂ} {q : ℝ}
    (h : dispersion b p q ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun x => root b x q) p :=
  (continuedRoot_analyticAt h).comp (f := fun x : ℂ × ℂ => dispersion b x q) (dispersion_analyticAt b p q)

theorem dispersion_continuous (b : ℝ) :
    Continuous (fun x : (ℂ × ℂ) × ℝ => dispersion b x.1 x.2) := by
  unfold dispersion
  fun_prop

theorem root_continuousAt {b : ℝ} {p : ℂ × ℂ} {q : ℝ}
    (h : dispersion b p q ∈ continuedRootDomain) :
    ContinuousAt (fun x : (ℂ × ℂ) × ℝ => root b x.1 x.2) (p,q) :=
  (continuedRoot_analyticAt h).continuousAt.comp
    (f := fun x : (ℂ × ℂ) × ℝ => dispersion b x.1 x.2) (dispersion_continuous b).continuousAt

theorem rootPair_continuousAt {b : ℝ} {B : ℂ} (hb : |b| < 1)
    (hB : 0 < B.im) (q : ℝ × ℝ) :
    ContinuousAt (fun x : (ℂ × ℂ) × (ℝ × ℝ) => rootPair b x.1 x.2) ((0,B),q) := by
  have hr (t : ℝ) := root_continuousAt (show dispersion b (0,B) t ∈ continuedRootDomain by
    simpa using edgeW_domain hb hB t)
  have h₁ := (hr q.1).comp (x := ((0,B),q))
    (f := fun x : (ℂ × ℂ) × (ℝ × ℝ) => (x.1,x.2.1))
    (continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd))
  have h₂ := (hr q.2).comp (x := ((0,B),q))
    (f := fun x : (ℂ × ℂ) × (ℝ × ℝ) => (x.1,x.2.2))
    (continuousAt_fst.prodMk (continuousAt_snd.comp continuousAt_snd))
  exact (h₁.sub h₂).div (continuousAt_const.sub (h₁.mul h₂))
    (by simpa using edgeRoot_pair_denominator_ne_zero hb hB q.1 q.2)

theorem completePair_continuousAt {b : ℝ} {B : ℂ} (hb : |b| < 1)
    (hB : 0 < B.im) (q : ℝ × ℝ) :
    ContinuousAt (fun x : (ℂ × ℂ) × (ℝ × ℝ) => completePair b x.1 x.2) ((0,B),q) := by
  have hr (t : ℝ) := root_continuousAt (show dispersion b (0,B) t ∈ continuedRootDomain by
    simpa using edgeW_domain hb hB t)
  have h₁ := (hr q.1).comp (x := ((0,B),q))
    (f := fun x : (ℂ × ℂ) × (ℝ × ℝ) => (x.1,x.2.1))
    (continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd))
  have h₂ := (hr q.2).comp (x := ((0,B),q))
    (f := fun x : (ℂ × ℂ) × (ℝ × ℝ) => (x.1,x.2.2))
    (continuousAt_fst.prodMk (continuousAt_snd.comp continuousAt_snd))
  unfold completePair
  apply (continuousAt_snd.comp continuousAt_fst).mul
  apply continuousAt_canceledPair _ _ _ _ ((0,B),q) (by fun_prop) (by fun_prop) h₁ h₂
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  simpa using edgeRoot_pair_denominator_ne_zero hb hB q.1 q.2

/-- One common two-complex-dimensional neighborhood controls all real angles.
The roots need not stay in the unit disk on this neighborhood. -/
theorem independent_parameter_neighborhood {b : ℝ} {B : ℂ}
    (hb : |b| < 1) (hB : 0 < B.im) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ 0 < C ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (0,B),
        (∀ q ∈ Icc (-Real.pi) Real.pi, dispersion b p q ∈ continuedRootDomain) ∧
        (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          ‖rootPair b p (q,t)‖ ≤ r ∧ ‖completePair b p (q,t)‖ ≤ C) := by
  obtain ⟨r,hr,hr1,hm⟩ := edgeRoot_uniform_schur hb hB
  have hroot : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,B),
      ∀ q ∈ Icc (-Real.pi) Real.pi, dispersion b p q ∈ continuedRootDomain := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro q _
    exact (dispersion_continuous b).continuousAt.eventually
      (continuedRootDomain_isOpen.mem_nhds (by simpa using edgeW_domain hb hB q))
  let K : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hp : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,B), ∀ q ∈ K, ‖rootPair b p q‖ < (r+1)/2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    apply (rootPair_continuousAt hb hB q).norm.eventually_lt continuousAt_const
    have hh := hm q.1 hq.1 q.2 hq.2
    simp only [rootPair,root_zero]
    linarith
  have hc : ContinuousOn (completePair b (0,B)) K := by
    intro q _
    exact ((completePair_continuousAt hb hB q).comp
      (f := fun q : ℝ × ℝ => (((0:ℂ),B),q))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  let C := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right M 0]
  have hc' : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,B), ∀ q ∈ K, ‖completePair b p q‖ < C := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    apply (completePair_continuousAt hb hB q).norm.eventually_lt continuousAt_const
    exact (hM q hq).trans_lt (by dsimp [C]; linarith [le_max_left M 0])
  refine ⟨(r+1)/2,C,by positivity,by linarith,hC,?_⟩
  filter_upwards [hroot,hp,hc'] with p hpd hpr hpc
  exact ⟨hpd,fun q hq t ht => ⟨(hpr (q,t) ⟨hq,ht⟩).le,(hpc (q,t) ⟨hq,ht⟩).le⟩⟩

/-- An actual common polydisk, with the radius chosen before either independent
complex parameter and before the angular variables. -/
theorem independent_parameter_polydisk {b : ℝ} {B₀ : ℂ}
    (hb : |b| < 1) (hB : 0 < B₀.im) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ r < 1 ∧ 0 < C ∧
      ∀ u B : ℂ, ‖u‖ < δ → ‖B-B₀‖ < δ →
        (∀ q ∈ Icc (-Real.pi) Real.pi, dispersion b (u,B) q ∈ continuedRootDomain) ∧
        (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          ‖rootPair b (u,B) (q,t)‖ ≤ r ∧ ‖completePair b (u,B) (q,t)‖ ≤ C) := by
  obtain ⟨r,C,hr,hr1,hC,he⟩ := independent_parameter_neighborhood hb hB
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,r,C,hδ,hr,hr1,hC,fun u B hu hBB => hd ?_⟩
  simpa only [mem_ball,Prod.dist_eq,dist_zero_right,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,max_lt_iff] using And.intro hu hBB

/-- Any genuinely holomorphic variable-anisotropy family can be inserted into
the independent polydisk without freezing its anisotropy. -/
theorem variable_family_root_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : ℝ} {u B : E → ℂ} {x : E} {q : ℝ}
    (hu : AnalyticAt ℂ u x) (hB : AnalyticAt ℂ B x)
    (hW : dispersion b (u x,B x) q ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun y => root b (u y,B y) q) x :=
  (root_analyticAt hW).comp (f := fun y => (u y,B y)) (hu.prod hB)

/-- Compact admissible complex anisotropies have a common normal-coordinate disk
and common constants.  This is proved by compactness in `B` and the complete
angular square simultaneously, not by choosing one disk for each curve. -/
theorem compact_parameter_disk {b : ℝ} {K : Set ℂ}
    (hb : |b| < 1) (hK : IsCompact K) (hB : ∀ B ∈ K, 0 < B.im) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ r < 1 ∧ 0 < C ∧
      ∀ u B : ℂ, ‖u‖ < δ → B ∈ K →
        (∀ q ∈ Icc (-Real.pi) Real.pi, dispersion b (u,B) q ∈ continuedRootDomain) ∧
        (∀ q ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          ‖rootPair b (u,B) (q,t)‖ ≤ r ∧ ‖completePair b (u,B) (q,t)‖ ≤ C) := by
  let L : Set (ℂ × (ℝ × ℝ)) := K ×ˢ (Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi)
  have hL : IsCompact L := hK.prod (isCompact_Icc.prod isCompact_Icc)
  have hp (x : ℂ × (ℝ × ℝ)) (hx : x ∈ L) :
      ContinuousAt (fun y : ℂ × (ℂ × (ℝ × ℝ)) => rootPair b (y.1,y.2.1) y.2.2) (0,x) :=
    (rootPair_continuousAt hb (hB x.1 hx.1) x.2).comp
      (x := ((0:ℂ),x))
      (f := fun y : ℂ × (ℂ × (ℝ × ℝ)) => ((y.1,y.2.1),y.2.2))
      (by fun_prop)
  have hc (x : ℂ × (ℝ × ℝ)) (hx : x ∈ L) :
      ContinuousAt (fun y : ℂ × (ℂ × (ℝ × ℝ)) => completePair b (y.1,y.2.1) y.2.2) (0,x) :=
    (completePair_continuousAt hb (hB x.1 hx.1) x.2).comp
      (x := ((0:ℂ),x))
      (f := fun y : ℂ × (ℂ × (ℝ × ℝ)) => ((y.1,y.2.1),y.2.2))
      (by fun_prop)
  have hp0 : ContinuousOn (fun x : ℂ × (ℝ × ℝ) => rootPair b (0,x.1) x.2) L := by
    intro x hx
    exact ((hp x hx).comp (f := fun x : ℂ × (ℝ × ℝ) => ((0:ℂ),x))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hc0 : ContinuousOn (fun x : ℂ × (ℝ × ℝ) => completePair b (0,x.1) x.2) L := by
    intro x hx
    exact ((hc x hx).comp (f := fun x : ℂ × (ℝ × ℝ) => ((0:ℂ),x))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨r,hr,hr1,hrb⟩ := compact_norm_strict_bound L _ hL hp0 (by
    intro x hx
    obtain ⟨r,_,hr,hbound⟩ := edgeRoot_uniform_schur hb (hB x.1 hx.1)
    exact (show ‖rootPair b (0,x.1) x.2‖ ≤ r by
      simpa [rootPair] using hbound x.2.1 hx.2.1 x.2.2 hx.2.2).trans_lt hr)
  obtain ⟨M,hM⟩ := hL.exists_bound_of_continuousOn hc0
  let C := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right M 0]
  have hp' : ∀ᶠ u : ℂ in 𝓝 0, ∀ x ∈ L, ‖rootPair b (u,x.1) x.2‖ < (r+1)/2 := by
    apply hL.eventually_forall_of_forall_eventually
    intro x hx
    exact (hp x hx).norm.eventually_lt continuousAt_const (by linarith [hrb x hx])
  have hc' : ∀ᶠ u : ℂ in 𝓝 0, ∀ x ∈ L, ‖completePair b (u,x.1) x.2‖ < C := by
    apply hL.eventually_forall_of_forall_eventually
    intro x hx
    exact (hc x hx).norm.eventually_lt continuousAt_const
      ((hM x hx).trans_lt (by dsimp [C]; linarith [le_max_left M 0]))
  have hd : ∀ᶠ u : ℂ in 𝓝 0, ∀ x ∈ K ×ˢ Icc (-Real.pi) Real.pi,
      dispersion b (u,x.1) x.2 ∈ continuedRootDomain := by
    apply (hK.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro x hx
    have hcont : ContinuousAt (fun y : ℂ × (ℂ × ℝ) => dispersion b (y.1,y.2.1) y.2.2) (0,x) := by
      unfold dispersion
      fun_prop
    exact hcont.eventually (continuedRootDomain_isOpen.mem_nhds
      (by simpa using edgeW_domain hb (hB x.1 hx.1) x.2))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp (hd.and (hp'.and hc'))
  refine ⟨δ,(r+1)/2,C,hδ,by positivity,by linarith,hC,?_⟩
  intro u B hu hBK
  obtain ⟨hd,hp,hc⟩ := hδb (show u ∈ ball (0:ℂ) δ by simpa using hu)
  exact ⟨fun q hq => hd (B,q) ⟨hBK,hq⟩,
    fun q hq t ht => ⟨(hp (B,(q,t)) ⟨hBK,hq,ht⟩).le,
      (hc (B,(q,t)) ⟨hBK,hq,ht⟩).le⟩⟩

end
end IsingBulk.Joint.RegularEdges
