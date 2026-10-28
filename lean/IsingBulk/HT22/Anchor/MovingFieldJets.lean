import IsingBulk.HT22.Anchor.MovingGenerator
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem frameJet_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω,F z.1 z.2=G z.1 z.2) (xs : List (Option (Fin N)))
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m F xs s θ=preferredFrameJet τ p m G xs s θ := by
  induction xs generalizing s θ with
  | nil => exact he (s,θ) hz
  | cons a xs ih =>
    rw [preferredFrameJet_cons,preferredFrameJet_cons]
    exact preferredFrameStep_congr_open τ p m a _ _ Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz

theorem source_fixed_anchor_moving_adapter {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m t θ) :
    residualField anchor t (sourceCoordinate τ p m t θ)=
      fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t θ) anchor := by
  have ht (i : Fin N) := correctedUDot_eq_inverseT t (sourceCoordinate τ p m t θ i)
    (framePoint_inverse_analytic h i) (preferredMovingBranch_analyticAt_upper t h.trace_im).differentiableAt
  simp only [sourceCoordinate_moving_adapter] at ht
  unfold residualField fixedAnchorInMovingCoordinates
  simp only [←ht,Tail.inverseV_moving_adapter,sourceCoordinate_moving_adapter]

theorem branch_velocity_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) :
    PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => deriv preferredMovingBranch z.1) Ω := by
  intro z hz
  have ha := (preferredMovingBranch_analyticAt_upper z.1 (hpoint z hz).trace_im).deriv
  exact ⟨(ha.contDiffAt.restrict_scalars ℝ).comp z contDiffAt_fst,ha.differentiableAt⟩

theorem movingSourceResidual_mixed {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) (i : Fin N) :
    PreferredMixedSmoothOn (fun z => movingSourceResidual anchor τ p m z.1 z.2 i) Ω :=
  ((source_generator_factors_mixed anchor τ δ p m hp hm Ω hpoint).2.2.2 i).sub
    (branch_velocity_mixed τ δ p m Ω hpoint)

/-- Quantitative moving-field estimate; both terms are actual primitive frame
jets, not bounds on a generated transport descendant. -/
theorem movingSourceResidual_frame_bound {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-δ) δ)
    (xs : List (Option (Fin N))) (i : Fin N) (A B : ℝ)
    (hA : ‖preferredFrameJet τ p m (fun t x =>
      fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t x) anchor i) xs s θ‖≤A)
    (hB : ‖preferredFrameJet τ p m (fun t _ => deriv preferredMovingBranch t) xs s θ‖≤B) :
    ‖preferredFrameJet τ p m (fun t x => movingSourceResidual anchor τ p m t x i) xs s θ‖≤A+B := by
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ)
  have hpts : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => hΩsub hz
  let F := fun t x => residualField anchor t (sourceCoordinate τ p m t x) i
  let G := fun t (_ : Fin N → ℝ) => deriv preferredMovingBranch t
  have hF := (source_generator_factors_mixed anchor τ δ p m hp hm Ω hpts).2.2.2 i
  have hG := branch_velocity_mixed τ δ p m Ω hpts
  have he : preferredFrameJet τ p m F xs s θ=preferredFrameJet τ p m
      (fun t x => fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t x) anchor i) xs s θ :=
    frameJet_congr_open τ p m _ _ Ω hΩ
      (fun z hz => congrFun (source_fixed_anchor_moving_adapter anchor τ δ p m z.1 z.2 (hpts z hz)) i) xs s θ hz
  have hneg := (PreferredMixedSmoothOn.const Ω (-1)).mul hG
  have hs := preferredFrameJet_add τ δ p m hp hm Ω hΩ hpts F (fun t x => (-1:ℂ)*G t x)
    hF hneg xs s θ hz
  have hf : (fun t x => movingSourceResidual anchor τ p m t x i)=fun t x => F t x+(-1:ℂ)*G t x := by
    funext t x
    simp only [movingSourceResidual,F,G,neg_one_mul,sub_eq_add_neg]
  rw [hf,hs,preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hpts G hG (-1) xs s θ hz]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_neg,norm_one,one_mul]
  exact add_le_add (he ▸ hA) hB
/-- All genuine frame jets of the correctly transformed fixed-v anchor field
have only linear particle cost, with one epsilon regime before all jet orders. -/
theorem actual_moving_anchor_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,θ a≤ -d.b-δB/2 →
      ∀ xs : List (Option (Fin N)),xs.length≤J → ∀ i,
      ‖preferredFrameJet τ B.p B.m
        (fun t x => movingSourceResidual a τ B.p B.m t x i) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ) := by
  obtain ⟨cap,hcap,hcapa,hanchor⟩ := actual_fixed_anchor_frame_jets d
  obtain ⟨εb,hεb,hbranch⟩ := actual_branch_velocity_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εa,τa,hεa,hτa,haj⟩ := hanchor B hB δB hδB
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨min εa (min εb εf),min τa τf,
    lt_min hεa (lt_min hεb hεf),lt_min hτa hτf,?_⟩
  intro J
  obtain ⟨A,hA,hAj⟩ := haj J
  choose D hD hDj using hbranch
  let M := 1+∑ j∈Finset.range (J+1),D j
  have hM : 0<M := by
    have hh := Finset.sum_nonneg (fun j (_ : j∈Finset.range (J+1)) => zero_le_one.trans (hD j))
    dsimp [M]; linarith
  have hDM (j : ℕ) (hj : j≤J) : D j≤M := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => zero_le_one.trans (hD k))
      (show j∈Finset.range (J+1) by simp; omega)
    dsimp [M]; linarith
  refine ⟨A+M,add_pos hA hM,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ a ha xs hxs i
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε
    (hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ
    (hτr.trans_le (min_le_right _ _)) θ hθ
  have hf := hAj N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
    (hτr.trans_le (min_le_left _ _)) θ hθ a ha xs hxs i
  obtain ⟨hb,hbj⟩ := hDj xs.length ε hε
    (hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hg := branch_velocity_frame_bound τ δ B.p B.m B.smooth B.m_smooth _ θ hpoint hstrict
    xs M hM.le hb (hbj.trans (hDM xs.length hxs))
  have hh := movingSourceResidual_frame_bound a τ δ B.p B.m B.smooth B.m_smooth _ θ hpoint hstrict
    xs i (A*(N:ℝ)) M hf hg
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hmN := mul_le_mul_of_nonneg_left hN1 hM.le
  nlinarith

end
end IsingBulk.HT22.Anchor
