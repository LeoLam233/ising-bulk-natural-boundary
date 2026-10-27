import IsingBulk.Preferred22.SelectedOneBodyProfile
import IsingBulk.Preferred22.NegativeCoarea
import IsingBulk.Preferred22.SelectedRegularGap

/-! The independent angular majorant on the actual deformed contour.
The branch estimate uses the literal outward normal form, and the remaining
angles form a compact set uniformly separated from both true branches. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1400000

theorem preferred_outward_discriminant_lower (d : PreferredBranchData) :
    ∃ c r : ℝ,0<c ∧ 0<r ∧ ∀ ε δ u : ℝ,
      0<ε → ε<r → 0≤δ → δ<r → |u|<r →
      c*(|u|+ε+δ)≤‖(outwardPlateauW d ε δ u)^2-1‖ := by
  obtain ⟨c,C,r₀,hc,_,hr₀,hmod⟩ := IsingBulk.Branch.current_modulus_Q d.localData
  obtain ⟨rd,hrd,hdom⟩ := preferred_outward_branch_domain d
  let r := min (outwardTransferRadius d r₀) rd
  have hr : 0<r := lt_min (outwardTransferRadius_pos d hr₀) hrd
  refine ⟨c,r,hc,hr,?_⟩
  intro ε δ u hε hεr hδ hδr hu
  have hrt : r≤outwardTransferRadius d r₀ := min_le_left _ _
  have hrd' : r≤rd := min_le_right _ _
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d hr₀ hε
    (hεr.trans_le hrt) hδ (hδr.trans_le hrt) (hu.trans_le hrt)
  have hnorm := (hmod ε (δ+d.localData.c₀*ε) u hε he ht ht' hu').1
  rw [outwardPlateauD_transfer] at hnorm
  change c*(|u|+ε+2*(δ+d.localData.c₀*ε))≤‖1-outwardPlateauW d ε δ u‖ at hnorm
  have hsmall : c*(|u|+ε+δ)≤‖outwardPlateauW d ε δ u-1‖ := by
    rw [norm_sub_rev]
    nlinarith [mul_nonneg d.localData.c₀_pos.le hε.le]
  have hre := (hdom ε δ u hε (hεr.trans_le hrd') hδ
    (hδr.trans_le hrd') (hu.trans_le hrd')).1
  have hlarge : 1≤‖outwardPlateauW d ε δ u+1‖ := by
    have hh := Complex.re_le_norm (outwardPlateauW d ε δ u+1)
    simp only [Complex.add_re,Complex.one_re] at hh
    linarith
  have heq : (outwardPlateauW d ε δ u)^2-1 =
      (outwardPlateauW d ε δ u-1)*(outwardPlateauW d ε δ u+1) := by ring
  rw [heq,norm_mul]
  exact hsmall.trans (le_mul_of_one_le_right (norm_nonneg _) hlarge)

lemma preferred_bump_angle_reflection (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ σ υ θ : ℝ) :
    preferredBumpAngle B.m B.p τ σ υ θ =
      -preferredBumpAngle B.m B.p τ υ σ (-θ) := by
  simp only [preferredBumpAngle,PreferredCoareaBump.m,neg_neg]
  push_cast
  ring

def preferredSelectedAwayAngles (d : PreferredBranchData) (r : ℝ) : Set ℝ :=
  Icc (-Real.pi) Real.pi ∩ {θ : ℝ | r≤|θ+d.b| ∧ r≤|θ-d.b|}

lemma preferred_selected_away_compact (d : PreferredBranchData) (r : ℝ) :
    IsCompact (preferredSelectedAwayAngles d r) := by
  apply isCompact_Icc.inter_right
  exact (isClosed_le continuous_const ((continuous_id.add continuous_const).abs : Continuous (fun θ : ℝ => |θ+d.b|))).inter
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs : Continuous (fun θ : ℝ => |θ-d.b|)))

lemma preferred_selected_reference_discriminant_ne_zero (d : PreferredBranchData)
    {r θ : ℝ} (hr : 0<r) (hθ : θ∈preferredSelectedAwayAngles d r) :
    (preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1≠0 := by
  have hcos : Real.cos d.b≠Real.cos θ := by
    intro hh
    have he : d.b=|θ| := Real.injOn_cos ⟨d.b_pos.le,d.b_lt.le⟩
      ⟨abs_nonneg θ,abs_le.mpr hθ.1⟩ (by rwa [Real.cos_abs])
    by_cases hp : 0≤θ
    · rw [abs_of_nonneg hp] at he
      have h := hθ.2.2
      rw [←he,sub_self,abs_zero] at h
      linarith
    · rw [abs_of_neg (lt_of_not_ge hp)] at he
      have h := hθ.2.1
      have hz : θ+d.b=0 := by linarith
      rw [hz,abs_zero] at h
      linarith
  have hlarge : 0<2+Real.cos d.b-Real.cos θ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi d.b_pos.le (le_refl Real.pi) d.b_lt
    rw [Real.cos_pi] at h
    linarith [Real.cos_le_one θ]
  have heq : (preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1 =
      ((Real.cos d.b-Real.cos θ:ℝ):ℂ)*((2+Real.cos d.b-Real.cos θ:ℝ):ℂ) := by
    rw [preferredRadialTrace_zero,←Complex.ofReal_cos]
    push_cast
    ring
  rw [heq]
  exact mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr hcos) (by exact_mod_cast ne_of_gt hlarge)

theorem preferred_selected_away_reference_gap (d : PreferredBranchData)
    {r : ℝ} (hr : 0<r) :
    ∃ γ : ℝ,0<γ ∧ ∀ θ∈preferredSelectedAwayAngles d r,
      γ≤‖(preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1‖ := by
  let K := preferredSelectedAwayAngles d r
  have hK : IsCompact K := preferred_selected_away_compact d r
  by_cases hn : K.Nonempty
  · have hc : Continuous (fun θ : ℝ => ‖(preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1‖) := by fun_prop
    obtain ⟨θ,hθ,hmin⟩ := hK.exists_isMinOn hn hc.continuousOn
    exact ⟨_,norm_pos_iff.mpr (preferred_selected_reference_discriminant_ne_zero d hr hθ),hmin⟩
  · exact ⟨1,zero_lt_one,fun θ hθ => (hn ⟨θ,hθ⟩).elim⟩

theorem preferred_selected_away_source_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {r : ℝ} (hr : 0<r) :
    ∃ γ ρ : ℝ,0<γ ∧ 0<ρ ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<ρ → |τ|<ρ → σ∈Icc 0 1 → υ∈Icc 0 1 →
      θ∈preferredSelectedAwayAngles d r →
      γ≤‖(preferredRadialTrace d ε-Complex.cos
        (preferredBumpAngle B.m B.p τ σ υ θ))^2-1‖ := by
  obtain ⟨γ,hγ,hbase⟩ := preferred_selected_away_reference_gap d hr
  let K : Set (ℝ × ℝ × ℝ) := preferredSelectedAwayAngles d r ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hK : IsCompact K := (preferred_selected_away_compact d r).prod
    (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℝ := fun x y =>
    ‖(preferredRadialTrace d x.1-Complex.cos
      (preferredBumpAngle B.m B.p x.2 y.2.1 y.2.2 y.1))^2-1‖
  have hcont (y : ℝ × ℝ × ℝ) :
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0),y) := by
    have hp : Continuous B.p := B.smooth.continuous
    have hm : Continuous B.m := hp.comp continuous_neg
    unfold F preferredBumpAngle preferredRadialTrace IsingBulk.Branch.radialParameter
    fun_prop (disch := simp)
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ),∀ y∈K,γ/2<F x y := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hzero : F (0,0) y=‖(preferredRadialTrace d 0-Complex.cos (y.1:ℂ))^2-1‖ := by
      simp [F,preferredBumpAngle]
    have hb : γ/2<F (0,0) y := by rw [hzero]; linarith [hbase y.1 hy.1]
    exact continuousAt_const.eventually_lt (hcont y) hb
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨γ/2,ρ,by positivity,hρ,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθ
  have hdist : dist (ε,τ) ((0,0):ℝ × ℝ)<ρ := by
    change dist (ε,τ) (0:ℝ × ℝ)<ρ
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ
  exact (hball hdist (θ,σ,υ) ⟨hθ,hσ,hυ⟩).le

theorem preferred_selected_source_discriminant_profile (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ ε τ σ υ θ : ℝ,
      0<ε → ε<ρ → 0≤τ → τ<ρ → σ∈Icc 0 1 → υ∈Icc 0 1 →
      θ∈Icc (-Real.pi) Real.pi →
      c*(|Real.cos d.b-Real.cos θ|+ε)≤
        ‖(preferredRadialTrace d ε-Complex.cos
          (preferredBumpAngle B.m B.p τ σ υ θ))^2-1‖ := by
  obtain ⟨a,ra,ha,hra,hloc⟩ := preferred_outward_discriminant_lower d
  let r := min ra (preferredBranchPlateauWidth d B)
  have hr : 0<r := lt_min hra (preferredBranchPlateauWidth_pos d B)
  have hrra : r≤ra := min_le_left _ _
  have hrplateau : r≤preferredBranchPlateauWidth d B := min_le_right _ _
  obtain ⟨g,rg,hg,hrg,hfar⟩ := preferred_selected_away_source_gap d B hr
  let ρ := min 1 (min ra rg)
  let c := min a (g/3)
  have hρ : 0<ρ := lt_min zero_lt_one (lt_min hra hrg)
  have hc : 0<c := lt_min ha (by positivity)
  have hca : c≤a := min_le_left _ _
  have hcg : c≤g/3 := min_le_right _ _
  have hρa : ρ≤ra := (min_le_right _ _).trans (min_le_left _ _)
  have hρg : ρ≤rg := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,ρ,hc,hρ,min_le_left _ _,?_⟩
  intro ε τ σ υ θ hε hερ hτ hτρ hσ hυ hθ
  have hnear (σ υ θ : ℝ) (hσ : σ∈Icc 0 1) (_hυ : υ∈Icc 0 1)
      (hu : |θ+d.b|<r) :
      c*(|Real.cos d.b-Real.cos θ|+ε)≤
        ‖(preferredRadialTrace d ε-Complex.cos
          (preferredBumpAngle B.m B.p τ σ υ θ))^2-1‖ := by
    have hδ : 0≤τ*σ := mul_nonneg hτ hσ.1
    have hδa : τ*σ<ra := (mul_le_of_le_one_right hτ hσ.2).trans_lt (hτρ.trans_le hρa)
    have hp := preferred_actual_plateau_angle d B τ σ υ (hu.trans_le hrplateau)
    have hangle : preferredBumpAngle B.m B.p τ σ υ θ = outwardPlateauAngle d (τ*σ) (θ+d.b) := by
      simpa only [show -d.b+(θ+d.b)=θ by ring] using hp
    rw [hangle,preferredRadialTrace,←outwardPlateauW_formula]
    have hb := hloc ε (τ*σ) (θ+d.b) hε (hερ.trans_le hρa) hδ hδa (hu.trans_le hrra)
    have hcos := Real.abs_cos_sub_cos_le (-d.b) θ
    rw [Real.cos_neg,show -d.b-θ=-(θ+d.b) by ring,abs_neg] at hcos
    calc
      c*(|Real.cos d.b-Real.cos θ|+ε) ≤ a*(|Real.cos d.b-Real.cos θ|+ε) :=
        mul_le_mul_of_nonneg_right hca (by positivity)
      _ ≤ a*(|θ+d.b|+ε+τ*σ) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ ≤ _ := hb
  by_cases hlo : |θ+d.b|<r
  · exact hnear σ υ θ hσ hυ hlo
  by_cases hhi : |θ-d.b|<r
  · have hneg : |-θ+d.b|<r := by
      rwa [show -θ+d.b=-(θ-d.b) by ring,abs_neg]
    have hb := hnear υ σ (-θ) hυ hσ hneg
    rw [Real.cos_neg] at hb
    rw [preferred_bump_angle_reflection d B τ σ υ θ,Complex.cos_neg]
    exact hb
  · have hb := hfar ε τ σ υ θ (by rw [abs_of_pos hε]; exact hερ.trans_le hρg)
        (by rw [abs_of_nonneg hτ]; exact hτρ.trans_le hρg) hσ hυ
        ⟨hθ,le_of_not_gt hlo,le_of_not_gt hhi⟩
    have hε1 : ε≤1 := (hερ.trans_le (min_le_left _ _)).le
    have hcos : |Real.cos d.b-Real.cos θ|≤2 := by
      have hh := abs_sub_le (Real.cos d.b) 0 (Real.cos θ)
      simp only [sub_zero,zero_sub,abs_neg] at hh
      linarith [Real.abs_cos_le_one d.b,Real.abs_cos_le_one θ]
    calc
      c*(|Real.cos d.b-Real.cos θ|+ε) ≤ c*3 :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ ≤ g := by linarith
      _ ≤ _ := hb

lemma preferred_oneBody_of_discriminant_margin {W : ℂ} (hW : OffRealSegment W)
    {c X : ℝ} (hc : 0<c) (hX : 0<X) (hgap : c*X≤‖W^2-1‖) :
    ‖oneBody (physicalRoot W)‖≤(Real.sqrt c)⁻¹*(Real.sqrt X)⁻¹ := by
  have he := congrArg (fun z : ℂ => ‖z‖) (preferred_oneBody_discriminant hW)
  rw [norm_pow,norm_inv] at he
  have hbound : ‖oneBody (physicalRoot W)‖^2≤(c*X)⁻¹ := by
    rw [he]
    exact inv_anti₀ (mul_pos hc hX) hgap
  have hs : ((Real.sqrt c)⁻¹*(Real.sqrt X)⁻¹)^2=(c*X)⁻¹ := by
    rw [mul_pow,inv_pow,inv_pow,Real.sq_sqrt hc.le,Real.sq_sqrt hX.le,mul_inv]
  have hn : 0≤(Real.sqrt c)⁻¹*(Real.sqrt X)⁻¹ := by positivity
  nlinarith [norm_nonneg (oneBody (physicalRoot W))]

end
end IsingBulk.Preferred22
