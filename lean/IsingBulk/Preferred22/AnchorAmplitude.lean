import IsingBulk.Preferred22.AnchorKernel
import IsingBulk.Preferred22.AnchorProductGap
import IsingBulk.Preferred22.NormalConvergence

/-! The complete literal regular amplitude on the anchored contour. The
product resolvent is retained inside the analytic amplitude and the exact
factorial/Haar normalizer is kept throughout. Uniform joint neighborhoods
are constructed from a genuine compact anchor before all particle orders. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- This is the literal regular amplitude already used by the physical
seed identity; no alternative normalization is introduced. -/
abbrev preferredAnchorAmplitude {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : ℂ :=
  preferredRegularAmplitude s q

theorem preferredRegularProductPhase_eq_prod {N : ℕ} (s : ℂ) (q : Fin N → ℂ) :
    preferredRegularProductPhase s q=∏ i,preferredRegularDiskRoot s (q i) := by
  simp only [preferredRegularProductPhase,preferredRegularDiskRoot,Finset.mul_sum,Complex.exp_sum]

theorem preferred_regular_oneBody_germ_at (s q : ℂ)
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hcos : Complex.cos ((q+preferredMovingBranch s)/2)≠0)
    (hφ : (preferredRegularPhase s q).im<0) :
    (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) =ᶠ[𝓝 (s,q)]
      (fun z => preferredOneBodyExtension z.1 z.2) := by
  have hBa : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch) hB analyticAt_fst
  have hca := (Complex.analyticAt_cos.comp ((analyticAt_snd.add hBa).div_const (c := (2:ℂ)))).continuousAt
  have hpa := (preferredRegularPhase_analyticAt s q hU hB).continuousAt
  have hc := hca.eventually_ne hcos
  have hp := (Complex.continuous_im.continuousAt.comp hpa).eventually_lt continuousAt_const hφ
  filter_upwards [hU.eventually_analyticAt,hc,hp] with z hzU hzc hzφ
  apply preferredRegularOneBody_eq_extension z.1 z.2 hzc
  · exact (AnalyticAt.comp (f := fun u : ℂ => (z.1,u))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hzU
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact preferred_sine_ne_zero_of_neg_im _ hzφ

/-- Uniform genuine scalar neighborhoods and an actual named-anchor root
gap on the complete one-sided source. -/
theorem preferred_actual_anchor_scalar_balls (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ η C q₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<η ∧ 1≤C ∧ 0≤q₀ ∧ q₀<1 ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      (∀ i,
        (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) =ᶠ[𝓝 (s,q i)]
          (fun z => preferredOneBodyExtension z.1 z.2) ∧
        AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (closedBall (s,q i) η) ∧
        (∀ z∈closedBall (s,q i) η,‖preferredOneBodyExtension z.1 z.2‖≤C) ∧
        AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) (closedBall (s,q i) η) ∧
        (∀ z∈closedBall (s,q i) η,‖preferredRegularDiskRoot z.1 z.2‖≤C) ∧
        ‖(preferredRegularDiskRoot s (q i))⁻¹‖≤C ∧
        ‖preferredRegularDiskRoot s (q i)‖≤1) ∧
      ∀ anchor,θ anchor≤ -d.b-δB/2 → ‖preferredRegularDiskRoot s (q anchor)‖≤q₀ := by
  obtain ⟨cap,hcap,hcapa,hdom⟩ := preferred_actual_whole_inverse_partition d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨R,L,ρ,κ,εd,τd,c,hR,hL,hρ,hκ,hεd,hτd,_hc,hgood,hleft,hsource⟩ := hdom B hB δB hδB
  let D := R∪L
  have hD : IsCompact D := hR.union hL
  have hscalar (s q : ℂ) (hs : ‖s-preferredSelectedPoint d‖<ρ) (hq : q∈D) :
      AnalyticAt ℂ preferredMovingBranch s ∧
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
      Complex.cos ((q+preferredMovingBranch s)/2)≠0 ∧
      preferredOneBodyGap s q≠0 := by
    rcases hq with hq|hq
    · have hg := hgood s q q hs hq hq
      exact ⟨hg.1,hg.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.1⟩
    · have hg := hleft s q hs hq
      exact ⟨hg.1,hg.2.1,hg.2.2.2.1,hg.2.2.2.2.1⟩
  let K := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D
  have hK : IsCompact K := (isCompact_closedBall _ _).prod hD
  have hmem {z : ℂ × ℂ} (hz : z∈K) : ‖z.1-preferredSelectedPoint d‖<ρ := by
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by simpa only [mem_closedBall,dist_eq_norm] using hz.1
    linarith
  have haa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) K := by
    intro z hz
    have hg := hscalar z.1 z.2 (hmem hz) hz.2
    exact preferredOneBodyExtension_analyticAt _ _ hg.2.1 hg.1 hg.2.2.2
  have hza : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) K := by
    intro z hz
    have hg := hscalar z.1 z.2 (hmem hz) hz.2
    exact preferredRegularDiskRoot_analyticAt _ _ hg.2.1 hg.1
  have hia : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => (preferredRegularDiskRoot z.1 z.2)⁻¹) K := by
    intro z hz
    exact (hza z hz).inv (Complex.exp_ne_zero _)
  obtain ⟨ηA,CA,hηA,hCA,hAb⟩ := preferred_compact_analytic_balls _ K hK haa
  obtain ⟨ηZ,CZ,hηZ,hCZ,hZb⟩ := preferred_compact_analytic_balls _ K hK hza
  obtain ⟨CI,hCI,hIb⟩ := preferred_compact_scalar_all_jets _ K hK hia 0
  obtain ⟨q₀,hq₀,hq₀1,hgap⟩ := preferred_compact_left_root_gap d L hL ρ hρ hleft
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  let C := max CA (max CZ CI)
  have hCAC : CA≤C := le_max_left _ _
  have hCZC : CZ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCIC : CI≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min εd (min εf (ρ/2)),min τd τf,min ηA ηZ,C,q₀,
    lt_min hεd (lt_min hεf (half_pos hρ)),lt_min hτd hτf,lt_min hηA hηZ,
    hCA.trans hCAC,hq₀,hq₀1,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have heD : ε<εd := hεr.trans_le (min_le_left _ _)
  have heF : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htD : τ<τd := hτr.trans_le (min_le_left _ _)
  have htF : τ<τf := hτr.trans_le (min_le_right _ _)
  have hp := (hframe N hN ε τ hε heF hτ htF θ hθ).1
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact heρ.le
  have hqi (i : Fin N) : q i∈D := by
    rcases (hsource N hN ε τ hε heD hτ htD θ hθ i).1 with h|h
    · exact Or.inl (h (mem_closedBall_self hκ.le))
    · exact Or.inr (h (mem_closedBall_self hκ.le))
  have hz (i : Fin N) : (s,q i)∈K := ⟨by simpa only [mem_closedBall,dist_eq_norm] using hs,hqi i⟩
  constructor
  · intro i
    have hg := hscalar s (q i) (by linarith) (hqi i)
    refine ⟨preferred_regular_oneBody_germ_at s (q i) hg.1 hg.2.1 hg.2.2.1 (hp.phase_im_neg i),
      (hAb _ (hz i)).1.mono (closedBall_subset_closedBall (min_le_left _ _)),?_,
      (hZb _ (hz i)).1.mono (closedBall_subset_closedBall (min_le_right _ _)),?_,?_,
      (preferredRegularDiskRoot_source_norm hp i).le⟩
    · intro z hz'
      exact ((hAb _ (hz i)).2 z (closedBall_subset_closedBall (min_le_left _ _) hz')).trans hCAC
    · intro z hz'
      exact ((hZb _ (hz i)).2 z (closedBall_subset_closedBall (min_le_right _ _) hz')).trans hCZC
    · simpa only [norm_iteratedFDeriv_zero] using (hIb _ (hz i)).trans hCIC
  · intro anchor hanchor
    apply hgap s (q anchor) hs
    exact (hsource N hN ε τ hε heD hτ htD θ hθ anchor).2 hanchor (mem_closedBall_self hκ.le)

/-- The relative movement is derived from the analytic function bound by
Cauchy and the mean-value inequality. -/
theorem preferred_analytic_relative_movement {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x : E) (η C : ℝ) (hη : 0<η) (hC : 0≤C)
    (hf : AnalyticOnNhd ℂ f (closedBall x η))
    (hb : ∀ z∈closedBall x η,‖f z‖≤C)
    (hx : f x≠0) (hi : ‖(f x)⁻¹‖≤C) (y : E)
    (hy : y∈closedBall x (η/4)) :
    ‖f y/f x-1‖≤(4*C*C/η)*‖y-x‖ := by
  have hs : ball x (η/2)⊆closedBall x η :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  have hd : ∀ z∈ball x (η/2),‖fderiv ℂ f z‖≤4*C/η := by
    intro z hz
    exact analytic_fderiv_half_ball_bound f x η C hη (hf.mono ball_subset_closedBall)
      (fun w hw => hb w (ball_subset_closedBall hw)) z hz
  have hy' : y∈ball x (η/2) :=
    (closedBall_subset_ball (by linarith)).trans (Subset.refl _) hy
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf z (hs hz)).differentiableAt) hd (convex_ball x (η/2))
    (mem_ball_self (half_pos hη)) hy'
  have he : f y/f x-1=(f y-f x)*(f x)⁻¹ := by field_simp
  rw [he,norm_mul]
  calc
    _ ≤ ((4*C/η)*‖y-x‖)*C := mul_le_mul hh hi (norm_nonneg _) (by positivity)
    _ = _ := by ring


def PreferredAnchorScalarBallData {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (η C : ℝ) : Prop :=
  ∀ i,
    (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) =ᶠ[𝓝 (s,q i)]
      (fun z => preferredOneBodyExtension z.1 z.2) ∧
    AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (closedBall (s,q i) η) ∧
    (∀ z∈closedBall (s,q i) η,‖preferredOneBodyExtension z.1 z.2‖≤C) ∧
    AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) (closedBall (s,q i) η) ∧
    (∀ z∈closedBall (s,q i) η,‖preferredRegularDiskRoot z.1 z.2‖≤C) ∧
    ‖(preferredRegularDiskRoot s (q i))⁻¹‖≤C ∧
    ‖preferredRegularDiskRoot s (q i)‖≤1

def PreferredAnchorPairBallData {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (η C : ℝ) : Prop :=
  ∀ i j,∃ G : (ℂ × ℂ × ℂ) → ℂ,
    (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) =ᶠ[𝓝 (s,q i,q j)] G ∧
    AnalyticOnNhd ℂ G (closedBall (s,q i,q j) η) ∧
    ∀ z∈closedBall (s,q i,q j) η,‖G z‖≤C

/-- A uniform scalar/pair neighborhood and one actual anchor produce a
joint amplitude neighborhood of radius c/N. The full resolvent remains
analytic there, and the exact normalizer produces the genuine factorial
decay. Every datum is discharged by the following actual-source wrapper. -/
theorem preferred_anchor_amplitude_ball_of_data (η C q₀ : ℝ)
    (hη : 0<η) (hC : 1≤C) (hq₀ : 0≤q₀) (hq₀1 : q₀<1) :
    ∃ c H : ℝ,0<c ∧ 0<H ∧ ∀ N : ℕ,0<N → ∀ s : ℂ,∀ q : Fin N → ℂ,
      ∀ anchor : Fin N,
      PreferredAnchorScalarBallData s q η C → PreferredAnchorPairBallData s q η C →
      ‖preferredRegularDiskRoot s (q anchor)‖≤q₀ →
      ∃ F : (ℂ × (Fin N → ℂ)) → ℂ,
        (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2) =ᶠ[𝓝 (s,q)] F ∧
        AnalyticOnNhd ℂ F (closedBall (s,q) (c/(N:ℝ))) ∧
        ∀ z∈closedBall (s,q) (c/(N:ℝ)),
          ‖F z‖≤H*(Real.exp 1*C^2/Real.sqrt N)^N := by
  classical
  obtain ⟨a,ha,hgap⟩ := preferred_anchor_product_relative_gap hq₀ hq₀1
  let c := min (η/4) (a*η/(4*C*C))
  let q₁ := (1+q₀)/2
  let H := 2/(1-q₁)
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0<c := lt_min (by positivity) (by positivity)
  have hq₁ : 0≤q₁ := by dsimp [q₁]; positivity
  have hq₁1 : q₁<1 := by dsimp [q₁]; linarith
  have hH : 0<H := div_pos (by norm_num) (sub_pos.mpr hq₁1)
  refine ⟨c,H,hc,hH,?_⟩
  intro N hN s q anchor hscalar hpair hanchor
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hr : 0<c/(N:ℝ) := div_pos hc hNr
  have hrη : c/(N:ℝ)≤η/4 := (div_le_self hc.le hN1).trans (min_le_left _ _)
  choose G hGeq hGa hGb using hpair
  let Z : (ℂ × (Fin N → ℂ)) → ℂ := fun z => ∏ i,preferredRegularDiskRoot z.1 (z.2 i)
  let K : (ℂ × (Fin N → ℂ)) → Matrix (Fin N) (Fin N) ℂ :=
    fun z i j => G i j (z.1,z.2 i,z.2 j)
  let A : (ℂ × (Fin N → ℂ)) → ℂ := fun z => ∏ i,preferredOneBodyExtension z.1 (z.2 i)
  let F : (ℂ × (Fin N → ℂ)) → ℂ := fun z =>
    ((1+Z z)/(1-Z z))*(K z).det*A z/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))
  have hproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i : Fin N) :
      (z.1,z.2 i)∈closedBall (s,q i) (c/(N:ℝ)) := by
    rw [mem_closedBall,dist_eq_norm] at hz ⊢
    change ‖preferredOneProjection i z-preferredOneProjection i (s,q)‖≤c/(N:ℝ)
    rw [← map_sub]
    exact (preferredOneProjection_norm_le i _).trans hz
  have hpairproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i j : Fin N) :
      (z.1,z.2 i,z.2 j)∈closedBall (s,q i,q j) η := by
    rw [mem_closedBall,dist_eq_norm] at hz ⊢
    change ‖preferredPairProjection i j z-preferredPairProjection i j (s,q)‖≤η
    rw [← map_sub]
    exact (preferredPairProjection_norm_le i j _).trans (hz.trans (hrη.trans (by linarith)))
  have hscalarproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i : Fin N) :
      (z.1,z.2 i)∈closedBall (s,q i) η :=
    closedBall_subset_closedBall (hrη.trans (by linarith)) (hproj hz i)
  have hZbound {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : ‖Z z‖≤q₁ := by
    apply hgap N hN (fun i => preferredRegularDiskRoot s (q i))
      (fun i => preferredRegularDiskRoot z.1 (z.2 i)) anchor
      (fun _ => Complex.exp_ne_zero _) (fun i => (hscalar i).2.2.2.2.2.2) hanchor
    intro i
    have hh := preferred_analytic_relative_movement
      (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) (s,q i) η C hη hCp.le
      (hscalar i).2.2.2.1 (hscalar i).2.2.2.2.1 (Complex.exp_ne_zero _)
      (hscalar i).2.2.2.2.2.1 (z.1,z.2 i)
      (closedBall_subset_closedBall hrη (hproj hz i))
    have hdist : ‖(z.1,z.2 i)-(s,q i)‖≤c/(N:ℝ) := by
      simpa only [mem_closedBall,dist_eq_norm] using hproj hz i
    calc
      _ ≤ (4*C*C/η)*(c/(N:ℝ)) := hh.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
      _ ≤ (4*C*C/η)*((a*η/(4*C*C))/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (min_le_right _ _) hNr.le) (by positivity)
      _ = a/(N:ℝ) := by field_simp
  have hZne {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : 1-Z z≠0 := by
    intro he
    have hzz : Z z=1 := (sub_eq_zero.mp he).symm
    have hh := hZbound hz
    rw [hzz,norm_one] at hh
    linarith
  have hZana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : AnalyticAt ℂ Z z := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2)
      ((hscalar i).2.2.2.1 _ (hscalarproj hz i)) ((preferredOneProjection i).analyticAt z)
  have hKana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) :
      AnalyticAt ℂ (fun z => (K z).det) z := by
    have hentry (i j : Fin N) : AnalyticAt ℂ (fun z => K z i j) z :=
      AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j))
        (g := G i j) (hGa i j _ (hpairproj hz i j)) ((preferredPairProjection i j).analyticAt z)
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hentry (σ i) i)))
  have hAana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : AnalyticAt ℂ A z := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2)
      ((hscalar i).2.1 _ (hscalarproj hz i)) ((preferredOneProjection i).analyticAt z)
  refine ⟨F,?_,?_,?_⟩
  · have hg : ∀ᶠ z : ℂ × (Fin N → ℂ) in 𝓝 (s,q),∀ i j,
        preferredRegularPair z.1 (z.2 i) (z.2 j)=G i j (z.1,z.2 i,z.2 j) := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      have ht : Tendsto (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j))
          (𝓝 (s,q)) (𝓝 (s,q i,q j)) :=
        (show Continuous (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j)) by fun_prop).tendsto (s,q)
      exact ht.eventually (hGeq i j)
    have ha : ∀ᶠ z : ℂ × (Fin N → ℂ) in 𝓝 (s,q),∀ i,
        preferredRegularOneBody z.1 (z.2 i)=preferredOneBodyExtension z.1 (z.2 i) := by
      apply eventually_all.mpr
      intro i
      have ht : Tendsto (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
          (𝓝 (s,q)) (𝓝 (s,q i)) :=
        (show Continuous (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i)) by fun_prop).tendsto (s,q)
      exact ht.eventually (hscalar i).1
    filter_upwards [hg,ha] with z hzg hza
    have hmat : preferredRegularKernel z.1 z.2=K z := Matrix.ext (fun i j => hzg i j)
    simp only [preferredRegularAmplitude,preferredRegularProductPhase_eq_prod,hmat,hza]
    rfl
  · intro z hz
    exact ((((analyticAt_const.add (hZana hz)).div (analyticAt_const.sub (hZana hz))
      (hZne hz)).mul (hKana hz)).mul (hAana hz)).div_const
  · intro z hz
    have hres : ‖(1+Z z)/(1-Z z)‖≤H := by
      have hnum : ‖1+Z z‖≤2 := by
        have hh := norm_add_le (1:ℂ) (Z z)
        rw [norm_one] at hh
        linarith [hZbound hz]
      have hden : 1-q₁≤‖1-Z z‖ := by
        have hh := norm_sub_norm_le (1:ℂ) (Z z)
        rw [norm_one] at hh
        linarith [hZbound hz]
      rw [norm_div]
      exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hq₁1) hden)
    have hdet : ‖(K z).det‖≤(Real.sqrt N*C)^N :=
      determinant_bound hN (K z) hCp.le (fun i j => hGb i j _ (hpairproj hz i j))
    have hbody : ‖A z‖≤C^N := by
      rw [show A z=∏ i,preferredOneBodyExtension z.1 (z.2 i) from rfl,norm_prod]
      calc
        _ ≤ ∏ _i : Fin N,C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => (hscalar i).2.2.1 _ (hscalarproj hz i))
        _ = _ := by simp
    have hnorm : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))‖=
        (N.factorial:ℝ)*(2*Real.pi)^(N-1) := by
      simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_ofNat,abs_of_pos Real.pi_pos]
    have hfactor : (N.factorial:ℝ)≤(N.factorial:ℝ)*(2*Real.pi)^(N-1) :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [Real.two_le_pi]))
    have hraw : ‖F z‖≤H*(Real.sqrt N*C)^N*C^N/(N.factorial:ℝ) := by
      change ‖((1+Z z)/(1-Z z))*(K z).det*A z/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))‖≤_
      rw [norm_div,norm_mul,norm_mul,hnorm]
      calc
        _ ≤ (H*(Real.sqrt N*C)^N*C^N)/((N.factorial:ℝ)*(2*Real.pi)^(N-1)) :=
          div_le_div_of_nonneg_right
            (mul_le_mul (mul_le_mul hres hdet (norm_nonneg _) hH.le) hbody (norm_nonneg _) (by positivity))
            (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hfactor
    have he : H*(Real.sqrt N*C)^N*C^N/(N.factorial:ℝ)=
        H*((Real.sqrt N*C^2)^N/(N.factorial:ℝ)) := by
      rw [mul_assoc,← mul_pow]
      ring
    exact hraw.trans (he.le.trans (mul_le_mul_of_nonneg_left (sqrt_factorial_envelope hN (sq_nonneg C)) hH.le))

/-- The complete literal anchored amplitude has actual analytic germs on a
c/N joint ball and its true factorial-decay bound there. -/
theorem preferred_actual_anchor_amplitude_balls (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ c A H : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<c ∧ 0<A ∧ 0<H ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      ∃ F : (ℂ × (Fin N → ℂ)) → ℂ,
        (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2) =ᶠ[𝓝 (s,q)] F ∧
        AnalyticOnNhd ℂ F (closedBall (s,q) (c/(N:ℝ))) ∧
        ∀ z∈closedBall (s,q) (c/(N:ℝ)),‖F z‖≤H*(A/Real.sqrt N)^N := by
  obtain ⟨capS,hcapS,hcapSa,hscalar⟩ := preferred_actual_anchor_scalar_balls d
  obtain ⟨capK,hcapK,hcapKa,hkernel⟩ := preferred_actual_anchor_kernel_representatives d
  refine ⟨min capS capK,lt_min hcapS hcapK,(min_le_left _ _).trans_lt hcapSa,?_⟩
  intro B hB δB hδB
  obtain ⟨εS,τS,ηS,CS,q₀,hεS,hτS,hηS,hCS,hq₀,hq₀1,hs⟩ :=
    hscalar B (hB.trans_le (min_le_left _ _)) δB hδB
  obtain ⟨εK,τK,ηK,CK,hεK,hτK,hηK,hCK,hk⟩ :=
    hkernel B (hB.trans_le (min_le_right _ _)) δB hδB
  let η := min ηS ηK
  let C := max CS CK
  have hη : 0<η := lt_min hηS hηK
  have hC : 1≤C := hCS.trans (le_max_left _ _)
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨c,H,hc,hH,hball⟩ := preferred_anchor_amplitude_ball_of_data η C q₀ hη hC hq₀ hq₀1
  refine ⟨min εS εK,min τS τK,c,Real.exp 1*C^2,H,lt_min hεS hεK,lt_min hτS hτK,
    hc,by positivity,hH,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ anchor hanchor
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  obtain ⟨hsc,hgap⟩ := hs N hN ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) θ hθ
  have hsd : PreferredAnchorScalarBallData s q η C := by
    intro i
    rcases hsc i with ⟨he,ha,hab,hz,hzb,hi,hn⟩
    refine ⟨he,ha.mono (closedBall_subset_closedBall (min_le_left _ _)),?_,
      hz.mono (closedBall_subset_closedBall (min_le_left _ _)),?_,hi.trans (le_max_left _ _),hn⟩
    · intro z hz'
      exact (hab z (closedBall_subset_closedBall (min_le_left _ _) hz')).trans (le_max_left _ _)
    · intro z hz'
      exact (hzb z (closedBall_subset_closedBall (min_le_left _ _) hz')).trans (le_max_left _ _)
  have hkd : PreferredAnchorPairBallData s q η C := by
    intro i j
    obtain ⟨G,he,ha,hb⟩ := hk N hN ε τ hε (hεr.trans_le (min_le_right _ _))
      hτ (hτr.trans_le (min_le_right _ _)) θ hθ i j
    refine ⟨G,he,ha.mono (closedBall_subset_closedBall (min_le_right _ _)),?_⟩
    intro z hz
    exact (hb z (closedBall_subset_closedBall (min_le_right _ _) hz)).trans (le_max_right _ _)
  exact hball N hN s q anchor hsd hkd (hgap anchor hanchor)

/-- All fixed joint derivative orders of the literal normalized amplitude
are proved from one source neighborhood. The constants precede N and the
radial limit, and the factorial is never placed into a free constant. -/
theorem preferred_actual_anchor_amplitude_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2) (s,q) ∧
      ∀ j≤J,‖iteratedFDeriv ℂ j
        (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2) (s,q)‖≤
        (C/Real.sqrt N)^N*(N:ℝ)^J := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_anchor_amplitude_balls d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,c,A,H,hε₀,hτ₀,hc,hA,hH,hball⟩ := hsource B hB δB hδB
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro J
  let D := fun j : ℕ => cauchyJetConstant j*H/c^j
  have hD (j : ℕ) : 0<D j := by dsimp [D]; exact div_pos (mul_pos (cauchyJetConstant_pos j) hH) (pow_pos hc j)
  let M := 1+∑ j∈Finset.range (J+1),D j
  have hM : 1≤M := by
    have hh := Finset.sum_nonneg (fun j (_ : j∈Finset.range (J+1)) => (hD j).le)
    dsimp [M]
    linarith
  have hDM (j : ℕ) (hj : j≤J) : D j≤M := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => (hD k).le)
      (show j∈Finset.range (J+1) by simp; omega)
    dsimp [M]
    linarith
  let C := max 1 A*M
  have hC : 1≤C := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hM
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ anchor hanchor
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hr : 0<c/(N:ℝ) := div_pos hc hNr
  obtain ⟨F,heq,hFa,hFb⟩ := hball N hN ε τ hε hεr hτ hτr θ hθ anchor hanchor
  have hFat : AnalyticAt ℂ F (s,q) := hFa _ (mem_closedBall_self hr.le)
  refine ⟨hFat.congr heq.symm,?_⟩
  intro j hj
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := analytic_iteratedFDeriv_center_bound F (s,q) (c/(N:ℝ)) (H*(A/Real.sqrt N)^N) hr
    (hFa.mono ball_subset_closedBall) (fun z hz => hFb z (ball_subset_closedBall hz)) j
  have hid : cauchyJetConstant j*(H*(A/Real.sqrt N)^N)/(c/(N:ℝ))^j=
      D j*(A/Real.sqrt N)^N*(N:ℝ)^j := by
    dsimp only [D]
    simp only [div_pow]
    field_simp [hc.ne',hNr.ne',hsqrt.ne']
  rw [hid] at hh
  have hDMN : D j≤M^N := (hDM j hj).trans (le_self_pow₀ hM hN.ne')
  calc
    _ ≤ D j*(A/Real.sqrt N)^N*(N:ℝ)^j := hh
    _ ≤ M^N*(max 1 A/Real.sqrt N)^N*(N:ℝ)^J := by
      apply mul_le_mul
      · exact mul_le_mul hDMN (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (le_max_right _ _) hsqrt.le) N) (by positivity) (by positivity)
      · exact pow_le_pow_right₀ hN1 hj
      · positivity
      · positivity
    _ = _ := by
      rw [← mul_pow]
      congr 2
      dsimp [C]
      ring

/-- The literal source frame words of the complete anchored amplitude
inherit the joint Cauchy bounds without any diameter or epsilon loss. -/
theorem preferred_actual_anchor_amplitude_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      ∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ B.p B.m
        (fun t x => preferredRegularAmplitude t (preferredSourceCoordinate τ B.p B.m t x)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤(C/Real.sqrt N)^N*(N:ℝ)^J := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_anchor_amplitude_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εa,τa,hεa,hτa,hjets⟩ := hsource B hB δB hδB
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨min εa εf,min τa τf,lt_min hεa hεf,lt_min hτa hτf,?_⟩
  intro J
  obtain ⟨C,hC,hjet⟩ := hjets J
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ anchor hanchor xs hxs
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) θ hθ
  obtain ⟨ha,hb⟩ := hjet N hN ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) θ hθ anchor hanchor
  exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
    (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2)
    (fun z : ℂ × (Fin N → ℂ) => preferredRegularAmplitude z.1 z.2)
    (ContinuousLinearMap.id ℂ (ℂ × (Fin N → ℂ))) (fun _ => le_rfl) ha Filter.EventuallyEq.rfl xs
    ((C/Real.sqrt N)^N*(N:ℝ)^J) (by have hCp := zero_le_one.trans hC; positivity) (hb xs.length hxs)

end
end IsingBulk.Preferred22
