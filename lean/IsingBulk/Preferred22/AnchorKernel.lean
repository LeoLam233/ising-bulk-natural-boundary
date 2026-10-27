import IsingBulk.Preferred22.AnchorSourcePartition
import IsingBulk.Preferred22.AnchorScalarJets
import IsingBulk.Preferred22.RegularFrameJets
import IsingBulk.Preferred22.AnalyticCauchyBounds

/-! Uniform analytic representatives of the literal kernel on the complete
one-sided contour. Right/right pairs use the proved removable-branch
extension. Every pair touching the compact left region uses the original
kernel and its genuine nonzero denominator. The latter compact set is
restricted by the actual physical root norms, not by a false positivity
claim for the patched right-domain denominator. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A compact analytic locus supplies a fixed neighborhood and a zeroth
bound, both before any derivative order or particle count. -/
theorem preferred_compact_analytic_balls {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    (f : E → ℂ) (K : Set E) (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ x∈K,
      AnalyticOnNhd ℂ f (closedBall x r) ∧ ∀ y∈closedBall x r,‖f y‖≤C := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ f) hf
  have hT : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨C,hC⟩ := hT.exists_bound_of_continuousOn (fun y hy =>
    (hsub hy).continuousAt.continuousWithinAt)
  refine ⟨r,max 1 C,hr,le_max_left _ _,?_⟩
  intro x hx
  have hb : closedBall x r⊆cthickening r K := closedBall_subset_cthickening hx r
  exact ⟨fun y hy => hsub (hb hy),fun y hy => (hC y (hb hy)).trans (le_max_right _ _)⟩

theorem preferred_compact_continuous_sublevel {E : Type*} [TopologicalSpace E]
    (K : Set E) (hK : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K) (a : ℝ) :
    IsCompact ({x | f x≤a} ∩ K) := by
  obtain ⟨U,hU,heq⟩ := continuousOn_iff_isClosed.mp hf (Iic a) isClosed_Iic
  change IsCompact ((f⁻¹' Iic a)∩K)
  rw [heq]
  exact hK.inter_left hU

theorem preferredRegularDiskRoot_norm_le_one_phase {s q : ℂ}
    (h : ‖preferredRegularDiskRoot s q‖≤1) : (preferredRegularPhase s q).im≤0 := by
  apply Real.exp_le_one_iff.mp
  simpa [preferredRegularDiskRoot,Complex.norm_exp] using h

/-- The original pair quotient is jointly analytic as soon as the true
phase sum has negative imaginary part. -/
theorem preferredRegularPair_analyticAt (s q r : ℂ)
    (hq : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hr : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,r))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hφ : (preferredRegularPhase s q).im+(preferredRegularPhase s r).im<0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) (s,q,r) := by
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hp' : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,q,r) :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hUq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hq hp
  have hUr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hr hp'
  have hφq := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s q hq hB) hp
  have hφr := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
    (preferredRegularPhase_analyticAt s r hr hB) hp'
  have hs : Complex.sin ((preferredRegularPhase s q+preferredRegularPhase s r)/2)≠0 := by
    apply preferred_sine_ne_zero_of_neg_im
    simp only [Complex.div_ofNat_im,Complex.add_im]
    linarith
  have hden : Complex.sinh (Complex.I*(preferredRegularPhase s q+preferredRegularPhase s r)/2)≠0 := by
    rw [show Complex.I*(preferredRegularPhase s q+preferredRegularPhase s r)/2=
      ((preferredRegularPhase s q+preferredRegularPhase s r)/2)*Complex.I by ring,
      Complex.sinh_mul_I]
    exact mul_ne_zero hs Complex.I_ne_zero
  exact (Complex.analyticAt_sin.comp ((hUq.sub hUr).div_const (c := (2:ℂ)))).div
    (Complex.analyticAt_sinh.comp ((analyticAt_const.mul (hφq.add hφr)).div_const (c := (2:ℂ)))) hden

/-- The complete right/left source domain has one uniform pair radius and
bound. The representative is proved equal to the literal quotient as a
germ; its choice never changes that quotient's actual derivatives. -/
theorem preferred_whole_kernel_representatives_on_domains (d : PreferredBranchData)
    (R L : Set ℂ) (hR : IsCompact R) (hL : IsCompact L) (ρ c : ℝ) (hρ : 0<ρ)
    (hgood : ∀ s q r : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈R → r∈R →
      PreferredRightRegularPoint c s q r)
    (hleft : ∀ s q : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈L → PreferredLeftRegularPoint s q) :
    ∃ η C : ℝ,0<η ∧ 1≤C ∧ ∀ s q r : ℂ,
      ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈R∪L → r∈R∪L →
      (preferredRegularPhase s q).im<0 → (preferredRegularPhase s r).im<0 →
      ∃ G : (ℂ × ℂ × ℂ) → ℂ,
        (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) =ᶠ[𝓝 (s,q,r)] G ∧
        AnalyticOnNhd ℂ G (closedBall (s,q,r) η) ∧
        ∀ z∈closedBall (s,q,r) η,‖G z‖≤C := by
  let D := R∪L
  have hD : IsCompact D := hR.union hL
  have hscalar (s q : ℂ) (hs : ‖s-preferredSelectedPoint d‖<ρ) (hq : q∈D) :
      AnalyticAt ℂ preferredMovingBranch s ∧
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) := by
    rcases hq with hq|hq
    · exact ⟨(hgood s q q hs hq hq).1,(hgood s q q hs hq hq).2.1⟩
    · exact ⟨(hleft s q hs hq).1,(hleft s q hs hq).2.1⟩
  let KR := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ (R×ˢR)
  have hKR : IsCompact KR := (isCompact_closedBall _ _).prod (hR.prod hR)
  have hRa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) KR := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hz.1
    have hg := hgood z.1 z.2.1 z.2.2 (by linarith) hz.2.1 hz.2.2
    exact preferredKernelExtension_analyticAt _ _ _ hg.2.1 hg.2.2.1 hg.1 hg.2.2.2.2.2.2.2.2.2
  obtain ⟨ηR,CR,hηR,hCR,hRb⟩ := preferred_compact_analytic_balls _ KR hKR hRa
  let K₀ := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ ((L×ˢD)∪(D×ˢL))
  have hK₀ : IsCompact K₀ := (isCompact_closedBall _ _).prod ((hL.prod hD).union (hD.prod hL))
  have hmem {z : ℂ × ℂ × ℂ} (hz : z∈K₀) :
      ‖z.1-preferredSelectedPoint d‖<ρ ∧ z.2.1∈D ∧ z.2.2∈D := by
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hz.1
    refine ⟨by linarith,?_⟩
    rcases hz.2 with h|h
    · exact ⟨Or.inr h.1,h.2⟩
    · exact ⟨h.1,Or.inr h.2⟩
  have hrootq : ContinuousOn (fun z : ℂ × ℂ × ℂ => preferredRegularDiskRoot z.1 z.2.1) K₀ := by
    intro z hz
    have hg := hscalar z.1 z.2.1 (hmem hz).1 (hmem hz).2.1
    exact (AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
      (g := fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2)
      (preferredRegularDiskRoot_analyticAt _ _ hg.2 hg.1)
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))).continuousAt.continuousWithinAt
  have hrootr : ContinuousOn (fun z : ℂ × ℂ × ℂ => preferredRegularDiskRoot z.1 z.2.2) K₀ := by
    intro z hz
    have hg := hscalar z.1 z.2.2 (hmem hz).1 (hmem hz).2.2
    exact (AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
      (g := fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2)
      (preferredRegularDiskRoot_analyticAt _ _ hg.2 hg.1)
      (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))).continuousAt.continuousWithinAt
  let KL := {z : ℂ × ℂ × ℂ | max ‖preferredRegularDiskRoot z.1 z.2.1‖
    ‖preferredRegularDiskRoot z.1 z.2.2‖≤1} ∩ K₀
  have hKL : IsCompact KL := preferred_compact_continuous_sublevel K₀ hK₀ _
    (by
      intro z hz
      exact (hrootq z hz).norm.max (hrootr z hz).norm) 1
  have hLa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) KL := by
    intro z hz
    have hgq := hscalar z.1 z.2.1 (hmem hz.2).1 (hmem hz.2).2.1
    have hgr := hscalar z.1 z.2.2 (hmem hz.2).1 (hmem hz.2).2.2
    apply preferredRegularPair_analyticAt _ _ _ hgq.2 hgr.2 hgq.1
    have hqφ := preferredRegularDiskRoot_norm_le_one_phase ((le_max_left _ _).trans hz.1)
    have hrφ := preferredRegularDiskRoot_norm_le_one_phase ((le_max_right _ _).trans hz.1)
    rcases hz.2.2 with h|h
    · have hneg := (hleft z.1 z.2.1 (hmem hz.2).1 h.1).2.2.2.2.2
      linarith
    · have hneg := (hleft z.1 z.2.2 (hmem hz.2).1 h.2).2.2.2.2.2
      linarith
  obtain ⟨ηL,CL,hηL,hCL,hLb⟩ := preferred_compact_analytic_balls _ KL hKL hLa
  refine ⟨min ηR ηL,max CR CL,lt_min hηR hηL,hCR.trans (le_max_left _ _),?_⟩
  intro s q r hs hq hr hqφ hrφ
  have hs' : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  have hsball : s∈closedBall (preferredSelectedPoint d) (ρ/2) := by
    simpa only [mem_closedBall,dist_eq_norm] using hs
  by_cases hright : q∈R ∧ r∈R
  · refine ⟨(fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2),
      preferred_regular_pair_germ c s q r (hgood s q r hs' hright.1 hright.2) hqφ hrφ,?_,?_⟩
    · exact (hRb (s,q,r) ⟨hsball,hright.1,hright.2⟩).1.mono (closedBall_subset_closedBall (min_le_left _ _))
    · intro z hz
      exact ((hRb (s,q,r) ⟨hsball,hright.1,hright.2⟩).2 z (closedBall_subset_closedBall (min_le_left _ _) hz)).trans
        (le_max_left _ _)
  · have hl : (q,r)∈(L×ˢD)∪(D×ˢL) := by
      rcases hq with hq|hq
      · right
        exact ⟨Or.inl hq,hr.resolve_left (fun hr => hright ⟨hq,hr⟩)⟩
      · exact Or.inl ⟨hq,hr⟩
    have hz : (s,q,r)∈KL := ⟨max_le (preferredRegularDiskRoot_norm_lt_one hqφ).le
      (preferredRegularDiskRoot_norm_lt_one hrφ).le,hsball,hl⟩
    refine ⟨(fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2),Filter.EventuallyEq.rfl,?_,?_⟩
    · exact (hLb _ hz).1.mono (closedBall_subset_closedBall (min_le_right _ _))
    · intro z hz'
      exact ((hLb _ hz).2 z (closedBall_subset_closedBall (min_le_right _ _) hz')).trans
        (le_max_right _ _)

/-- Genuine complete one-sided kernel representatives, with one radius
and bound before N, epsilon and all actual occupancy values. -/
theorem preferred_actual_anchor_kernel_representatives (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ η C : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<η ∧ 1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) → ∀ i j,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      ∃ G : (ℂ × ℂ × ℂ) → ℂ,
        (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) =ᶠ[𝓝 (s,q i,q j)] G ∧
        AnalyticOnNhd ℂ G (closedBall (s,q i,q j) η) ∧
        ∀ z∈closedBall (s,q i,q j) η,‖G z‖≤C := by
  obtain ⟨cap,hcap,hcapa,hdom⟩ := preferred_actual_whole_inverse_partition d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨R,L,ρ,κ,εd,τd,c,hR,hL,hρ,hκ,hεd,hτd,_hc,hgood,hleft,hsource⟩ := hdom B hB δB hδB
  obtain ⟨η,C,hη,hC,hpair⟩ := preferred_whole_kernel_representatives_on_domains d R L hR hL ρ c hρ hgood hleft
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨min εd (min εf (ρ/2)),min τd τf,η,C,
    lt_min hεd (lt_min hεf (half_pos hρ)),lt_min hτd hτf,hη,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ i j
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have heD : ε<εd := hεr.trans_le (min_le_left _ _)
  have heF : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htD : τ<τd := hτr.trans_le (min_le_left _ _)
  have htF : τ<τf := hτr.trans_le (min_le_right _ _)
  have hp := (hframe N hN ε τ hε heF hτ htF θ hθ).1
  have hqi (i : Fin N) : q i∈R∪L := by
    rcases (hsource N hN ε τ hε heD hτ htD θ hθ i).1 with h|h
    · exact Or.inl (h (mem_closedBall_self hκ.le))
    · exact Or.inr (h (mem_closedBall_self hκ.le))
  exact hpair s (q i) (q j) (by rw [preferred_radial_distance,abs_of_pos hε]; exact heρ.le)
    (hqi i) (hqi j) (hp.phase_im_neg i) (hp.phase_im_neg j)

end
end IsingBulk.Preferred22
