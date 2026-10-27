import IsingBulk.Preferred22.SourceMixedFactors
import IsingBulk.Preferred22.SourceFrameGeometry

/-! Uniform actual regular-factor frame jets. The patched holomorphic
extensions are used only after proving equality of germs with the literal
positive-epsilon physical factors. Projection to two or three variables
keeps all constants independent of particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set Metric
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem analytic_iteratedFDeriv_comp_linear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : E →L[ℂ] F) (f : F → G) (x : E) (hf : AnalyticAt ℂ f (L x)) (n : ℕ) :
    iteratedFDeriv ℂ n (f ∘ L) x=
      (iteratedFDeriv ℂ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  let S := {y | AnalyticAt ℂ f y}
  have hS : IsOpen S := isOpen_analyticAt ℂ f
  have hLS : IsOpen (L⁻¹' S) := hS.preimage L.continuous
  have hs : L x∈S := hf
  have hc : ContDiffOn ℂ (n:ℕ∞ω) f S := fun y hy => hy.contDiffAt.contDiffWithinAt
  have hh := L.iteratedFDerivWithin_comp_right hc hS.uniqueDiffOn hLS.uniqueDiffOn hs le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hLS hs,
    iteratedFDerivWithin_of_isOpen n hS hs] at hh
  exact hh

def preferredRegularPair (s q r : ℂ) : ℂ :=
  Complex.sin ((preferredMovingInverse s q-preferredMovingInverse s r)/2) /
    Complex.sinh (Complex.I*(preferredRegularPhase s q+preferredRegularPhase s r)/2)

theorem preferred_regular_oneBody_germ (c : ℝ) (s q : ℂ)
    (h : PreferredRightRegularPoint c s q q)
    (hφ : (preferredRegularPhase s q).im<0) :
    (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) =ᶠ[𝓝 (s,q)]
      (fun z => preferredOneBodyExtension z.1 z.2) := by
  have hreg : ∀ᶠ z : ℂ × ℂ in 𝓝 (s,q), PreferredRightRegularPoint c z.1 z.2 z.2 := by
    exact ((show Continuous (fun z : ℂ × ℂ => (z.1,z.2,z.2)) by fun_prop).tendsto (s,q)).eventually
      ((preferredRightRegularPoint_isOpen c).mem_nhds h)
  have hph := (preferredRegularPhase_analyticAt s q h.2.1 h.1).continuousAt
  have him := (Complex.continuous_im.continuousAt.comp hph).eventually_lt continuousAt_const hφ
  filter_upwards [hreg,him] with z hz hzφ
  apply preferredRegularOneBody_eq_extension z.1 z.2 hz.2.2.2.2.2.1
  · exact (AnalyticAt.comp (f := fun u : ℂ => (z.1,u))
      (g := fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) hz.2.1
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact preferred_sine_ne_zero_of_neg_im _ hzφ

theorem preferred_regular_pair_germ (c : ℝ) (s q r : ℂ)
    (h : PreferredRightRegularPoint c s q r)
    (hφq : (preferredRegularPhase s q).im<0) (hφr : (preferredRegularPhase s r).im<0) :
    (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2) =ᶠ[𝓝 (s,q,r)]
      (fun z => preferredKernelExtension z.1 z.2.1 z.2.2) := by
  have hreg : ∀ᶠ z : ℂ × ℂ × ℂ in 𝓝 (s,q,r), PreferredRightRegularPoint c z.1 z.2.1 z.2.2 :=
    (preferredRightRegularPoint_isOpen c).mem_nhds h
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredRegularPhase z.1 z.2.1) (s,q,r) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
      (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
      (preferredRegularPhase_analyticAt s q h.2.1 h.1) (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
  have hr : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredRegularPhase z.1 z.2.2) (s,q,r) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
      (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2)
      (preferredRegularPhase_analyticAt s r h.2.2.1 h.1) (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))
  have hqi := (Complex.continuous_im.continuousAt.comp hq.continuousAt).eventually_lt continuousAt_const hφq
  have hri := (Complex.continuous_im.continuousAt.comp hr.continuousAt).eventually_lt continuousAt_const hφr
  filter_upwards [hreg,hqi,hri] with z hz hzq hzr
  simp only [Function.comp_def] at hzq hzr
  rcases hz with ⟨_,_,_,_,_,hcq,hcr,_,_,hden⟩
  have hφ : Complex.sin ((preferredRegularPhase z.1 z.2.1+preferredRegularPhase z.1 z.2.2)/2)≠0 := by
    apply preferred_sine_ne_zero_of_neg_im
    have he : ((preferredRegularPhase z.1 z.2.1+preferredRegularPhase z.1 z.2.2)/2).im=
        ((preferredRegularPhase z.1 z.2.1).im+(preferredRegularPhase z.1 z.2.2).im)/2 := by
      simp only [Complex.div_ofNat_im,Complex.add_im]
    rw [he]
    linarith
  exact preferred_half_kernel_extension_identity _ _ _ _ _
    (preferredRegular_dispersion _ _ hcq) (preferredRegular_dispersion _ _ hcr) hφ hden

theorem PreferredFramePoint.phase_im_neg {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {s : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m s θ) (i : Fin N) :
    (preferredRegularPhase s (preferredSourceCoordinate τ p m s θ i)).im<0 := by
  rw [preferred_source_regular_phase_eq s τ p m θ δ h.delta_pos h.delta_lt h.trace_re
    h.trace_cap h.angles h.upper i]
  exact (IsingBulk.Branch.lowerArccos_sheet_of_upper (h.upper i)).2.2.2

theorem preferredFrameDirections_norm_le {N : ℕ} (xs : List (Option (Fin N)))
    (k : Fin xs.length) : ‖preferredFrameDirections xs k‖≤1 := by
  induction xs with
  | nil => exact Fin.elim0 k
  | cons a xs ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · cases a <;> simp [preferredFrameDirections,preferredComplexFrameDirection,Prod.norm_def,Pi.norm_single]
    · simpa only [preferredFrameDirections,Fin.cons_succ] using ih k

def preferredOneProjection {N : ℕ} (i : Fin N) : (ℂ × (Fin N → ℂ)) →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))

def preferredPairProjection {N : ℕ} (i j : Fin N) : (ℂ × (Fin N → ℂ)) →L[ℂ] ℂ × ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
    (((ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))

theorem preferredOneProjection_norm_le {N : ℕ} (i : Fin N) (z : ℂ × (Fin N → ℂ)) :
    ‖preferredOneProjection i z‖≤‖z‖ := by
  change max ‖z.1‖ ‖z.2 i‖≤max ‖z.1‖ ‖z.2‖
  exact max_le (le_max_left _ _) ((norm_le_pi_norm z.2 i).trans (le_max_right _ _))

theorem preferredPairProjection_norm_le {N : ℕ} (i j : Fin N) (z : ℂ × (Fin N → ℂ)) :
    ‖preferredPairProjection i j z‖≤‖z‖ := by
  change max ‖z.1‖ (max ‖z.2 i‖ ‖z.2 j‖)≤max ‖z.1‖ ‖z.2‖
  exact max_le (le_max_left _ _) (max_le
    ((norm_le_pi_norm z.2 i).trans (le_max_right _ _))
    ((norm_le_pi_norm z.2 j).trans (le_max_right _ _)))

theorem preferred_frame_analytic_projection_bound {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (F G : E → ℂ) (L : (ℂ × (Fin N → ℂ)) →L[ℂ] E)
    (hL : ∀ z, ‖L z‖≤‖z‖)
    (hG : AnalyticAt ℂ G (L (s,preferredSourceCoordinate τ p m s θ)))
    (heq : F =ᶠ[𝓝 (L (s,preferredSourceCoordinate τ p m s θ))] G)
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (hbound : ‖iteratedFDeriv ℂ xs.length G (L (s,preferredSourceCoordinate τ p m s θ))‖≤C) :
    ‖preferredFrameJet τ p m
      (fun t x => F (L (t,preferredSourceCoordinate τ p m t x))) xs s θ‖≤C := by
  let z := (s,preferredSourceCoordinate τ p m s θ)
  have hF : AnalyticAt ℂ F (L z) := hG.congr heq.symm
  have hFL : AnalyticAt ℂ (F ∘ L) z := hF.comp (L.analyticAt z)
  change ‖preferredFrameJet τ p m
    (fun t x => (F ∘ L) (t,preferredSourceCoordinate τ p m t x)) xs s θ‖≤C
  rw [preferredFrameJet_pullback τ δ p m hp hm s θ hpoint hθ (F ∘ L) hFL xs,
    preferredComplexFrameJet_eq_iteratedFDeriv (F ∘ L) xs z hFL]
  have he := heq.comp_tendsto (L.continuous.tendsto z)
  rw [(he.iteratedFDeriv ℂ xs.length).eq_of_nhds,
    analytic_iteratedFDeriv_comp_linear L G z hG xs.length]
  change ‖iteratedFDeriv ℂ xs.length G (L z)
    (fun k => L (preferredFrameDirections xs k))‖≤C
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length G (L z)‖ *
        ∏ k, ‖L (preferredFrameDirections xs k)‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C*1 := mul_le_mul hbound
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ =>
        (hL _).trans (preferredFrameDirections_norm_le xs k))) (by positivity) hC
    _ = _ := mul_one C

theorem preferred_regular_frame_jets_on_domain {N : ℕ} (d : PreferredBranchData)
    (ρ c : ℝ) (D : Set ℂ) (hρ : 0<ρ)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hs : ‖s-preferredSelectedPoint d‖≤ρ/2)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (ha : ∀ q∈D, ‖iteratedFDeriv ℂ xs.length
      (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (s,q)‖≤C)
    (hK : ∀ q∈D, ∀ r∈D, ‖iteratedFDeriv ℂ xs.length
      (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (s,q,r)‖≤C) :
    (∀ i, ‖preferredFrameJet τ p m
      (fun t x => preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤C) ∧
    (∀ i j, ‖preferredFrameJet τ p m
      (fun t x => preferredSourceRegularKernel τ p m t x i j) xs s θ‖≤C) := by
  have hs' : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  constructor
  · intro i
    have hg := hgood s _ _ hs' (hq i) (hq i)
    exact preferred_frame_analytic_projection_bound τ δ p m hp hm s θ hpoint hθ
      (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2)
      (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (preferredOneProjection i)
      (preferredOneProjection_norm_le i)
      (preferredOneBodyExtension_analyticAt s _ hg.2.1 hg.1 hg.2.2.2.2.2.2.2.1)
      (preferred_regular_oneBody_germ c s _ hg (hpoint.phase_im_neg i)) xs C hC (ha _ (hq i))
  · intro i j
    have hg := hgood s _ _ hs' (hq i) (hq j)
    exact preferred_frame_analytic_projection_bound τ δ p m hp hm s θ hpoint hθ
      (fun z : ℂ × ℂ × ℂ => preferredRegularPair z.1 z.2.1 z.2.2)
      (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (preferredPairProjection i j)
      (preferredPairProjection_norm_le i j)
      (preferredKernelExtension_analyticAt s _ _ hg.2.1 hg.2.2.1 hg.1 hg.2.2.2.2.2.2.2.2.2)
      (preferred_regular_pair_germ c s _ _ hg (hpoint.phase_im_neg i) (hpoint.phase_im_neg j))
      xs C hC (hK _ (hq i) _ (hq j))

/-- Every fixed-order literal source frame jet of a regular one-body factor
or pair entry is uniformly bounded on the whole right source. The same
physical thresholds precede all orders, N and occupancies; no diameter loss
or particle-count factor is required for these individual factors. -/
theorem preferred_actual_regular_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        ∀ xs : List (Option (Fin N)), xs.length≤j →
        (∀ i, ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredRegularOneBody t (preferredSourceCoordinate τ B.p B.m t x i)) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C) ∧
        (∀ i k, ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredSourceRegularKernel τ B.p B.m t x i k) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C) := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨δ,εf,τf,hδ,hδa,hεf,hτf,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min r (min (ρ/2) εf)
  let τ₀ := min r τf
  let δB := min (B.delta/2) (r/2)
  have hδB : 0<δB := lt_min (half_pos B.delta_pos) (half_pos hr)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt (by linarith [B.delta_pos])
  refine ⟨ε₀,τ₀,δB,lt_min hr (lt_min (half_pos hρ) hεf),lt_min hr hτf,hδB,hδBB,?_⟩
  choose C hC hCa hCK using preferred_regular_domain_all_jets d ρ c D hρ hDc (interior_subset hzero) hgood
  intro j
  let Cj := 1+∑ k∈Finset.range (j+1), C k
  have hsum : 0≤∑ k∈Finset.range (j+1), C k := Finset.sum_nonneg (fun k _ => (hC k).le)
  have hCj : 0<Cj := by dsimp [Cj]; linarith
  refine ⟨Cj,hCj,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
  have hepsρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsf : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ht : τ<r := hτr.trans_le (min_le_left _ _)
  have htf : τ<τf := hτr.trans_le (min_le_right _ _)
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hepsρ.le
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈D := by
    apply interior_subset
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using ht) hpocc hmocc
      (by have hh := (hθ i).1; have hd : δB≤r/2 := min_le_right _ _; linarith)
      (by have hh := (hθ i).2; linarith)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hepsf hτ htf θ hθ
  have hCk : C xs.length≤Cj := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (j+1)) => (hC k).le)
      (show xs.length∈Finset.range (j+1) by simp; omega)
    dsimp only [Cj]
    linarith
  exact preferred_regular_frame_jets_on_domain d ρ c D hρ hgood τ δ B.p B.m B.smooth B.m_smooth
    s θ hpoint hθstrict hs hq xs Cj hCj.le
    (fun q hq => (hCa xs.length s q hs hq).trans hCk)
    (fun q hq r hr => (hCK xs.length s q r hs hq hr).trans hCk)

end
end IsingBulk.Preferred22
