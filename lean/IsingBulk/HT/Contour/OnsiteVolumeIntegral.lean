import IsingBulk.HT.Contour.OnsiteLieIntegration
import IsingBulk.Tail.MixedVolumeMajorant
import IsingBulk.Tail.OriginalDensityMajorant

/-! Uniform L1 control of the actual full onsite branch volume. Every branch
coordinate is bounded by the one-dimensional square-root majorant, with
coupled occupancy still present. No phase coordinate is omitted. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem deformedPoint_effective_strength {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (θ : Fin N → ℝ) :
    deformedPoint f r (lam*τ) 1 θ=deformedPoint f r τ lam θ := by
  funext i
  have he : (1:ℝ)*retractionShift (lam*τ) (fun j => f.p (θ j)) (fun j => f.m (θ j)) i=
      lam*retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i := by
    unfold retractionShift
    ring
  simp only [deformedPoint,he]

def onsiteVolumeProductMajorant {N : ℕ} (b B eps : ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∏ i,mixedSpectatorMajorant b B eps (θ i)

theorem onsiteVolumeProductMajorant_nonneg {N : ℕ} (b : ℝ) {B : ℝ}
    (hB : 0≤B) (eps : ℝ) (θ : Fin N → ℝ) :
    0≤onsiteVolumeProductMajorant b B eps θ :=
  Finset.prod_nonneg (fun i _ => zero_le_one.trans (mixedSpectatorMajorant_one_le b hB (θ i)))

theorem onsiteVolumeProductMajorant_integral (N : ℕ) {b B eps : ℝ}
    (hb : 0≤b) (hb2 : b≤2*Real.pi) (hB : 0≤B) (he : 0<eps) :
    IntegrableOn (onsiteVolumeProductMajorant (N := N) b B eps) (angleBox N) ∧
      (∫ θ in angleBox N,onsiteVolumeProductMajorant b B eps θ)≤
        (2*Real.pi+4*B*Real.sqrt (2*Real.pi))^N := by
  have hc : Continuous (onsiteVolumeProductMajorant (N := N) b B eps) := by
    apply continuous_finsetProd
    intro i _
    exact (mixedSpectatorMajorant_continuous b B he).comp (continuous_apply i)
  refine ⟨hc.continuousOn.integrableOn_compact isCompact_Icc,?_⟩
  unfold onsiteVolumeProductMajorant
  rw [angleBox_restrict_pi,integral_fintype_prod_eq_prod]
  calc
    _ ≤ ∏ _i : Fin N,(2*Real.pi+4*B*Real.sqrt (2*Real.pi)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply integral_nonneg
        intro t
        exact zero_le_one.trans (mixedSpectatorMajorant_one_le b hB t)
      · intro i _
        exact (mixedSpectatorMajorant_integral hb hb2 hB he).2
    _ = _ := by simp

/-- All branch factors, including the empty or all-branch index sets, are
bounded. The effective strength lam*tau keeps the full [0,1] interval. -/
theorem onsite_actual_volume_product_majorant (d : LocalBranchData) :
    ∃ B e t₀ : ℝ,0<B ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∃ inner₀ : ℝ,0< inner₀ ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (J : Finset (Fin N)) (q : Fin N),
      0<N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      θ∈angleBox N →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      (∀ i∈J,θ i∈tsupport (sectorBranch d.thetaB inner hi)) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      ‖mixedHybridVolume J f r τ lam s θ‖≤onsiteVolumeProductMajorant d.thetaB B eps θ := by
  obtain ⟨B,R,t₀,hB,hR,ht,hBound⟩ := mixed_actual_branch_slope_majorant d
  refine ⟨B,R,t₀,hB,hR,ht,?_⟩
  intro η α hη hηsmall hα hαsmall
  obtain ⟨i₀,hi₀,hwidth⟩ := sector_branch_support_lower_chart d.thetaB_pos d.thetaB_lt
    (lt_min hR (half_pos hη))
  refine ⟨i₀,hi₀,?_⟩
  intro inner hi hinner N eps τ lam θ J q hN he heR hτ hl0 _hl1 htl hbox hSource hBranch
  have hsl (i : Fin N) (hiJ : i∈J) :
      ‖mixedSourceSlope (radialParameter d.theta eps)
        (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i)‖≤
        mixedSpectatorMajorant d.thetaB B eps (θ i) := by
    have hsin : Real.sin (θ i)≤3*α/2 := by
      rcases hSource with hO | hC
      · exact constructed_original_support_sine_upper d.thetaB η α hα i hO
      · exact constructed_current_support_sine_upper d.thetaB η α hα q i hC
    have hu := hwidth inner hi hinner (θ i) (hbox.1 i) (hbox.2 i)
      (show Real.sin (θ i)≤Real.sin d.thetaB/2 by linarith [d.a_pos]) (hBranch i hiJ)
    have hcore : lowerChord d.thetaB (θ i)<η^2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hu.le.trans (min_le_right _ _)) 2
      rw [sq_abs] at hs
      nlinarith [lowerChord_le_coordinate_square d.thetaB (θ i)]
    obtain ⟨hm,hp⟩ := constructed_lower_core_plateau d.a_pos hη hηsmall hα hcore.le
    have hb := hBound N eps (lam*τ) 1 _ θ i hN he heR.le (mul_nonneg hl0 hτ) htl
      (by norm_num) (by norm_num) (fun x => thresholdStep_range _ _ _) hp hm
      (hu.le.trans (min_le_left _ _))
    rw [deformedPoint_effective_strength] at hb
    have heq : θ i+d.thetaB-2*Real.pi=θ i-(2*Real.pi-d.thetaB) := by ring
    rw [heq] at hb
    exact hb.trans (by unfold mixedSpectatorMajorant; linarith)
  dsimp only
  rw [mixedHybridVolume,norm_prod]
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hsl).trans
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ J)
  · intro i _
    exact zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i))
  · intro i _ _
    exact mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i)

/-- Pure integration wrapper. The terminal theorem below proves its source
cover and pointwise estimate from the actual geometry. -/
theorem onsite_supported_volume_integral {n : ℕ} (J : Finset (Fin (n+1)))
    (f : SelectorFunctions) (hf : RegularSelector f) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    {s : ℂ} (w : (Fin (n+1) → ℝ) → ℂ)
    (hcover : ∀ θ∈tsupport w,(s,θ)∈onsiteLieDomain J f r τ lam)
    {b B eps : ℝ} (hb : 0≤b) (hb2 : b≤2*Real.pi) (hB : 0≤B) (he : 0<eps)
    (hpoint : ∀ θ∈angleBox (n+1) ∩ tsupport w,
      ‖mixedHybridVolume J f r τ lam s θ‖≤onsiteVolumeProductMajorant b B eps θ) :
    IntegrableOn (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖)
      (angleBox (n+1) ∩ tsupport w) ∧
    (∫ θ in angleBox (n+1),(tsupport w).indicator
      (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖) θ)≤
        (2*Real.pi+4*B*Real.sqrt (2*Real.pi))^(n+1) := by
  have hv : ContinuousOn (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖) (tsupport w) :=
    (((onsiteLie_volume_smooth J f hr τ lam hf.p_smooth hf.m_smooth).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hcover).norm)
  have hS : IsCompact (angleBox (n+1) ∩ tsupport w) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hint : IntegrableOn (fun θ : Fin (n+1) → ℝ => ‖mixedHybridVolume J f r τ lam s θ‖)
      (angleBox (n+1) ∩ tsupport w) :=
    (hv.mono inter_subset_right).integrableOn_compact hS
  obtain ⟨hmajor,hmajorbound⟩ := onsiteVolumeProductMajorant_integral (n+1) hb hb2 hB he
  refine ⟨hint,?_⟩
  rw [setIntegral_indicator (isClosed_tsupport w).measurableSet]
  apply (setIntegral_mono_on hint (hmajor.mono_set inter_subset_left)
    (measurableSet_Icc.inter (isClosed_tsupport w).measurableSet) hpoint).trans
  apply (setIntegral_mono_set hmajor
    (Filter.Eventually.of_forall (onsiteVolumeProductMajorant_nonneg b hB eps))
    (Filter.Eventually.of_forall (fun θ hθ => hθ.1))).trans hmajorbound

/-- Actual onsite branch-volume L1 bound, uniformly before all positive
particle orders and every homotopy slice. The two conclusions are the
original and named-current supports; no nonempty or proper-J condition is
imposed. The coupled occupancy is never replaced by an independent variable. -/
theorem onsite_actual_sector_volume_integrals (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ C e t₀ : ℝ,0<C ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∃ inner₀ : ℝ,0< inner₀ ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (n : ℕ) (eps τ lam : ℝ) (q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let V := mixedHybridVolume (mixedBranchIndexSet sigma) f r τ lam s
      let wK := onsiteOriginalSectorWeight f d.thetaB inner hi sigma
      let wS := onsiteNamedSectorWeight f d.thetaB inner hi q sigma τ
      (IntegrableOn (fun θ => ‖V θ‖) (angleBox (n+1) ∩ tsupport wK) ∧
        (∫ θ in angleBox (n+1),(tsupport wK).indicator (fun θ => ‖V θ‖) θ)≤C^(n+1)) ∧
      (IntegrableOn (fun θ => ‖V θ‖) (angleBox (n+1) ∩ tsupport wS) ∧
        (∫ θ in angleBox (n+1),(tsupport wS).indicator (fun θ => ‖V θ‖) θ)≤C^(n+1)) := by
  obtain ⟨B,eB,tB,hB,heB,htB,hmajor⟩ := onsite_actual_volume_product_majorant d
  obtain ⟨c,eD,tD,hc,_hcsmall,heD,htD,hcover⟩ := onsite_sector_support_covers d hcsmall
  refine ⟨2*Real.pi+4*B*Real.sqrt (2*Real.pi),min eB eD,min tB tD,
    by positivity,lt_min heB heD,lt_min htB htD,?_⟩
  intro η α hη hηsmall hα hαsmall
  obtain ⟨innerB,hinnerB,hmajor⟩ := hmajor η α hη hηsmall hα hαsmall
  refine ⟨min innerB ((Real.sin d.thetaB)^2/4),lt_min hinnerB (by positivity [d.a_pos]),?_⟩
  intro inner hi hinner n eps τ lam q sigma heps hepslt hτ hl0 hl1 htl
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hiB : inner≤ innerB := hinner.trans (min_le_left _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinner.trans (min_le_right _ _)
  have heB' : eps<eB := hepslt.trans_le (min_le_left _ _)
  have heD' : eps<eD := hepslt.trans_le (min_le_right _ _)
  have htB' : lam*τ<tB := htl.trans_le (min_le_left _ _)
  have htD' : lam*τ<tD := htl.trans_le (min_le_right _ _)
  obtain ⟨hcoverK,hcoverS⟩ := hcover η α inner hη hηsmall hα hαsmall hi his
    n eps τ lam q sigma heps heD' hτ hl0 hl1 htD'
  have hsU : s∈ball s (c*eps) := mem_ball_self (mul_pos hc heps)
  have hbranch (θ : Fin (n+1) → ℝ)
      (hassign : θ∈tsupport (sectorAssignmentWeight d.thetaB inner hi sigma)) :
      ∀ i∈J,θ i∈tsupport (sectorBranch d.thetaB inner hi) := by
    intro i hiJ
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    have he : sectorLabel d.thetaB inner hi (sigma i)=sectorBranch d.thetaB inner hi := by
      funext x
      simp only [hσ,sectorLabel,show (2:Fin 3) ≠ 0 by decide,
        show (2:Fin 3) ≠ 1 by decide,ite_false]
    simpa only [he] using hh
  constructor
  · apply onsite_supported_volume_integral J f hf (Real.exp_pos _) τ lam _
      (fun θ hθ => hcoverK ⟨hsU,hθ⟩) d.thetaB_pos.le
      (by linarith [d.thetaB_lt,Real.pi_pos]) hB.le heps
    intro θ hθ
    have hw := onsiteOriginalSectorWeight_support f d.thetaB inner hi sigma hθ.2
    exact hmajor inner hi hiB (n+1) eps τ lam θ J q (by omega) heps heB' hτ hl0 hl1 htB' hθ.1
      (Or.inl (tsupport_mul_subset_left hw)) (hbranch θ (tsupport_mul_subset_right hw))
  · apply onsite_supported_volume_integral J f hf (Real.exp_pos _) τ lam _
      (fun θ hθ => hcoverS ⟨hsU,hθ⟩) d.thetaB_pos.le
      (by linarith [d.thetaB_lt,Real.pi_pos]) hB.le heps
    intro θ hθ
    have hw := onsiteNamedSectorWeight_support f d.thetaB inner hi q sigma τ hθ.2
    exact hmajor inner hi hiB (n+1) eps τ lam θ J q (by omega) heps heB' hτ hl0 hl1 htB' hθ.1
      (Or.inr (tsupport_mul_subset_left hw)) (hbranch θ (tsupport_mul_subset_right hw))

end
end IsingBulk.HT.Contour
