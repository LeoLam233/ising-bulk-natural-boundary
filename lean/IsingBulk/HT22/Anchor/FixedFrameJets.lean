import IsingBulk.HT22.Anchor.FixedScalarJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual fixed-v anchor residual expressed as a function of (t,q).
It is not yet the moving-coordinate transport velocity, which also subtracts b'. -/
def fixedAnchorInMovingCoordinates {N : ℕ} (t : ℂ) (q : Fin N → ℂ) (a : Fin N) : Fin N → ℂ :=
  anchorField (fun i => correctedUDot t (q i)) (fun i => preferredSourceUQ t (q i)) a

theorem fixed_anchor_inverse_factors_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2) :
    (∀ i,PreferredMixedSmoothOn (fun z =>
      correctedUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) ∧
    (∀ a,PreferredMixedSmoothOn (fun z =>
      (preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 a))⁻¹) Ω) := by
  constructor
  · intro i
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun z : ℂ × (Fin N → ℂ) => correctedUDot z.1 (z.2 i))
    intro z hz
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i))
      (g := fun x : ℂ × ℂ => correctedUDot x.1 x.2)
      (correctedUDot_analyticAt _ _ ((hpoint z hz).inverse_analytic i)
        (preferredMovingBranch_analyticAt_upper z.1 (hpoint z hz).trace_im))
      ((preferredOneProjection i).analyticAt _)
  · intro a
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun z : ℂ × (Fin N → ℂ) => (preferredSourceUQ z.1 (z.2 a))⁻¹)
    intro z hz
    have h := hpoint z hz
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 a))
      (g := fun x : ℂ × ℂ => (preferredSourceUQ x.1 x.2)⁻¹)
      ((preferredSourceUQ_analyticAt_of_joint _ _ (h.inverse_analytic a)).inv (h.inverse_q_ne_zero a))
      ((preferredOneProjection a).analyticAt _)

theorem fixed_anchor_frame_bound_at {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-δ) δ) (a : Fin N) (J : ℕ) (C : ℝ) (hC : 0≤C)
    (hD : ∀ i,∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ p m (fun t x => correctedUDot t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤C)
    (hQ : ∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ p m (fun t x => (preferredSourceUQ t (preferredSourceCoordinate τ p m t x a))⁻¹) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) (i : Fin N) :
    ‖preferredFrameJet τ p m
      (fun t x => fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t x) a i) xs s θ‖≤
      (2^J*C^2)*(N:ℝ) := by
  classical
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ)
  have hΩpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => hΩsub hz
  obtain ⟨hDm,hQm⟩ := fixed_anchor_inverse_factors_mixed τ δ p m hp hm Ω hΩpoint
  let F := fun t x => ∑ b : Fin N,correctedUDot t (preferredSourceCoordinate τ p m t x b)
  let G := fun t x => (preferredSourceUQ t (preferredSourceCoordinate τ p m t x a))⁻¹
  have hFm : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω := PreferredMixedSmoothOn.sum hDm
  have hGm : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω := hQm a
  have hFb (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ p m F ys s θ‖≤(N:ℝ)*C := by
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hΩpoint _ hDm ys s θ hz]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _b : Fin N,C := Finset.sum_le_sum (fun b _ => hD b ys hys)
      _ = (N:ℝ)*C := by simp
  by_cases hi : i=a
  · subst i
    have he : (fun t x => fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t x) a a)=
        fun t x => (-1:ℂ)*(F t x*G t x) := by
      funext t x
      simp only [fixedAnchorInMovingCoordinates,anchorField,ite_true,F,G,div_eq_mul_inv]
      ring
    rw [he,preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hΩpoint _ (hFm.mul hGm) (-1) xs s θ hz]
    simp only [norm_mul,norm_neg,norm_one,one_mul]
    have hh := preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint F G hFm hGm s θ hz J
      ((N:ℝ)*C) C (by positivity) hC hFb hQ xs hxs
    exact hh.trans_eq (by ring)
  · have he : (fun t x => fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ p m t x) a i)=
        fun _ _ => (0:ℂ) := by
      funext t x
      simp only [fixedAnchorInMovingCoordinates,anchorField,ite_eq_right hi]
    rw [he,preferredFrameJet_const]
    split_ifs <;> simp only [norm_zero] <;> positivity

/-- The actual anchor field, including every real source frame, obeys its
uniform no-collision-loss estimate. Only its named fixed left separation
enters the constants; no field-jet bound is assumed. -/
theorem actual_fixed_anchor_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,θ a≤ -d.b-δB/2 →
      ∀ xs : List (Option (Fin N)),xs.length≤J → ∀ i,
      ‖preferredFrameJet τ B.p B.m
        (fun t x => fixedAnchorInMovingCoordinates t (preferredSourceCoordinate τ B.p B.m t x) a i) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*(N:ℝ) := by
  obtain ⟨cap,hcap,hcapa,hscalar⟩ := actual_fixed_scalar_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εa,τa,_q₀,hεa,hτa,_hq₀,_hq₀1,hscalar'⟩ := hscalar B hB δB hδB
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨min εa εf,min τa τf,lt_min hεa hεf,lt_min hτa hτf,?_⟩
  intro J
  choose A hA hAj using hscalar'
  let C := 1+∑ j∈Finset.range (J+1),A j
  have hsum : 0≤∑ j∈Finset.range (J+1),A j :=
    Finset.sum_nonneg (fun j _ => zero_le_one.trans (hA j))
  have hC : 0<C := by dsimp [C]; linarith
  have hAC (j : ℕ) (hj : j≤J) : A j≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => zero_le_one.trans (hA k))
      (show j∈Finset.range (J+1) by simp; omega)
    dsimp [C]
    linarith
  refine ⟨2^J*C^2,by positivity,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ a ha xs hxs i
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) θ hθ
  have hjet (b : Fin N) (j : ℕ) (_hj : j≤J) :=
    hAj j N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
      (hτr.trans_le (min_le_left _ _)) θ hθ b
  have hD (b : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ B.p B.m
        (fun t x => correctedUDot t (preferredSourceCoordinate τ B.p B.m t x b)) ys s θ‖≤C := by
    exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
      (fun z : ℂ × ℂ => correctedUDot z.1 z.2) (fun z : ℂ × ℂ => correctedUDot z.1 z.2)
      (preferredOneProjection b) (preferredOneProjection_norm_le b)
      (correctedUDot_analyticAt _ _ (hpoint.inverse_analytic b)
        (preferredMovingBranch_analyticAt_upper s hpoint.trace_im)) Filter.EventuallyEq.rfl ys C hC.le
      ((hjet b ys.length hys).2.1.trans (hAC ys.length hys))
  have hQ (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ B.p B.m
        (fun t x => (preferredSourceUQ t (preferredSourceCoordinate τ B.p B.m t x a))⁻¹) ys s θ‖≤C := by
    exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
      (fun z : ℂ × ℂ => (preferredSourceUQ z.1 z.2)⁻¹) (fun z : ℂ × ℂ => (preferredSourceUQ z.1 z.2)⁻¹)
      (preferredOneProjection a) (preferredOneProjection_norm_le a)
      ((preferredSourceUQ_analyticAt_of_joint _ _ (hpoint.inverse_analytic a)).inv (hpoint.inverse_q_ne_zero a))
      Filter.EventuallyEq.rfl ys C hC.le
      (((hjet a ys.length hys).2.2.2.2 ha).1.trans (hAC ys.length hys))
  exact fixed_anchor_frame_bound_at τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict a J C hC.le hD hQ xs hxs i

end
end IsingBulk.HT22.Anchor
