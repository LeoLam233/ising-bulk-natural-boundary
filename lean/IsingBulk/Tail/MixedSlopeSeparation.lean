import IsingBulk.Tail.ConstructedCurrentDisk
import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.NestedSectorPartition
import IsingBulk.Tail.OriginalCurrentPairTransferInput
import IsingBulk.Tail.OriginalDiskGlobalFactors

/-! Actual frozen-phase slope separation for nested source W profiles.
The outer margin is fixed before the true inner branch width. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology

theorem mixedSourcePhase_sin_norm_sq (s y : ℂ) :
    ‖Complex.sin (mixedSourcePhase s y)‖^2=‖1-(sourceW s y)^2‖ := by
  have hh := Complex.sin_sq_add_cos_sq (mixedSourcePhase s y)
  rw [show Complex.cos (mixedSourcePhase s y)=sourceW s y from cos_lowerArccos _] at hh
  have he : Complex.sin (mixedSourcePhase s y)^2=1-(sourceW s y)^2 := by linear_combination hh
  rw [← norm_pow,he]

theorem mixedSourceSlope_ratio_sq {s y v : ℂ}
    (hy : y-y⁻¹≠0) (hWy : 0<(sourceW s y).im) (hWv : 0<(sourceW s v).im) :
    ‖mixedSourceSlope s v/mixedSourceSlope s y‖^2 =
      (‖v-v⁻¹‖^2*‖1-(sourceW s y)^2‖)/(‖y-y⁻¹‖^2*‖1-(sourceW s v)^2‖) := by
  have hsy : ‖Complex.sin (mixedSourcePhase s y)‖≠0 := norm_ne_zero_iff.mpr (mixedSourcePhase_sin_ne hWy)
  have hsv : ‖Complex.sin (mixedSourcePhase s v)‖≠0 := norm_ne_zero_iff.mpr (mixedSourcePhase_sin_ne hWv)
  have hny : ‖y-y⁻¹‖≠0 := norm_ne_zero_iff.mpr hy
  rw [← mixedSourcePhase_sin_norm_sq s y,← mixedSourcePhase_sin_norm_sq s v]
  simp only [mixedSourceSlope,norm_div,norm_mul,Complex.norm_I,Complex.norm_ofNat,one_mul,div_pow,mul_pow]
  field_simp

theorem radialAnglePoint_difference_lower (v θ : ℝ) :
    2*|Real.sin θ| ≤ ‖radialAnglePoint v θ-(radialAnglePoint v θ)⁻¹‖ := by
  have he : (radialAnglePoint v θ)⁻¹=radialAnglePoint (-v) (-θ) := by
    rw [radialAnglePoint,← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have him : (radialAnglePoint v θ-(radialAnglePoint v θ)⁻¹).im=
      (Real.exp v+Real.exp (-v))*Real.sin θ := by
    rw [he]
    simp only [radialAnglePoint,Complex.sub_im,Complex.exp_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,sub_zero,zero_add,add_zero,Real.sin_neg]
    ring
  have hh := Complex.abs_im_le_norm (radialAnglePoint v θ-(radialAnglePoint v θ)⁻¹)
  rw [him,abs_mul,abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))] at hh
  have hsum : 2 ≤ Real.exp v+Real.exp (-v) := by linarith [Real.add_one_le_exp v,Real.add_one_le_exp (-v)]
  exact (mul_le_mul_of_nonneg_right hsum (abs_nonneg _)).trans hh

theorem radialAnglePoint_difference_upper {v : ℝ} (hv : |v|≤1) (θ : ℝ) :
    ‖radialAnglePoint v θ-(radialAnglePoint v θ)⁻¹‖ ≤ 2*Real.exp 1 := by
  have hy : ‖radialAnglePoint v θ‖=Real.exp v := radialAnglePoint_norm _ _
  have hi : ‖(radialAnglePoint v θ)⁻¹‖=Real.exp (-v) := by rw [norm_inv,hy,Real.exp_neg]
  have hh := norm_sub_le (radialAnglePoint v θ) (radialAnglePoint v θ)⁻¹
  rw [hy,hi] at hh
  have he := Real.exp_le_exp.mpr (abs_le.mp hv).2
  have he' := Real.exp_le_exp.mpr (show -v≤1 by linarith [(abs_le.mp hv).1])
  linarith

theorem sector_inner_sine_lower {b θ inner : ℝ} (hb : 0<Real.sin b)
    (hi : 0≤ inner) (hsmall : inner≤(Real.sin b)^2/4)
    (hprofile : |sectorDisplacement b θ|≤ inner) : Real.sin b/2 ≤ |Real.sin θ| := by
  have hd : |Real.cos θ-Real.cos b|≤ inner := by simpa only [sectorDisplacement,abs_sub_comm] using hprofile
  have hsum : |Real.cos θ+Real.cos b|≤2 := (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one θ,Real.abs_cos_le_one b])
  have hsq : |(Real.cos θ)^2-(Real.cos b)^2|≤2*inner := by
    rw [sq_sub_sq,abs_mul]
    simpa only [mul_comm] using mul_le_mul hd hsum (abs_nonneg _) hi
  have htrigθ := Real.sin_sq_add_cos_sq θ
  have htrigb := Real.sin_sq_add_cos_sq b
  have ha := (abs_le.mp hsq).2
  have hs := sq_abs (Real.sin θ)
  nlinarith [abs_nonneg (Real.sin θ)]

theorem mixed_slope_quarter_of_trace_gaps {s y v : ℂ} {b outer inner S : ℝ}
    (hb : 0<b) (ho : 0<outer) (hi : 0< inner) (hi1 : inner≤1) (hS : 0<S)
    (hchoose : inner≤b^2*outer*S/(4096*(Real.exp 1)^2))
    (hyn : b≤‖y-y⁻¹‖) (hvn : ‖v-v⁻¹‖≤2*Real.exp 1)
    (hyi : ‖sourceW s y-1‖≤2*inner)
    (hvminus : outer/4≤‖sourceW s v-1‖) (hvplus : S/2≤‖sourceW s v+1‖)
    (hWy : 0<(sourceW s y).im) (hWv : 0<(sourceW s v).im) :
    ‖mixedSourceSlope s v/mixedSourceSlope s y‖≤1/4 := by
  have hy0 : y-y⁻¹≠0 := norm_pos_iff.mp (hb.trans_le hyn)
  have hyplus : ‖sourceW s y+1‖≤2*inner+2 := by
    have hh := norm_add_le (sourceW s y-1) (2:ℂ)
    rw [show sourceW s y-1+2=sourceW s y+1 by ring] at hh
    norm_num at hh
    linarith
  have hnorm (W : ℂ) : ‖1-W^2‖=‖W-1‖*‖W+1‖ := by
    rw [show 1-W^2=-(W-1)*(W+1) by ring,norm_mul,norm_neg]
  have hinner : ‖1-(sourceW s y)^2‖≤8*inner := by
    rw [hnorm]
    have hh := mul_le_mul hyi hyplus (norm_nonneg _) (by positivity : 0≤2*inner)
    nlinarith
  have houter : outer*S/8≤‖1-(sourceW s v)^2‖ := by
    rw [hnorm]
    have hh := mul_le_mul hvminus hvplus (by positivity : 0≤S/2) (norm_nonneg _)
    nlinarith only [hh]
  have hnum : ‖v-v⁻¹‖^2*‖1-(sourceW s y)^2‖≤32*(Real.exp 1)^2*inner := by
    have hh := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hvn 2) hinner
      (norm_nonneg _) (by positivity : 0≤(2*Real.exp 1)^2)
    nlinarith only [hh]
  have hden : b^2*outer*S/8≤‖y-y⁻¹‖^2*‖1-(sourceW s v)^2‖ := by
    have hh := mul_le_mul (pow_le_pow_left₀ hb.le hyn 2) houter
      (by positivity : 0≤outer*S/8) (sq_nonneg _)
    nlinarith only [hh]
  have hd : 0<b^2*outer*S/8 := by positivity
  have hr := div_le_div₀ (by positivity : 0≤32*(Real.exp 1)^2*inner) hnum hd hden
  have hsmall : 32*(Real.exp 1)^2*inner/(b^2*outer*S/8) ≤ 1/16 := by
    apply (div_le_iff₀ hd).mpr
    have hh := (le_div_iff₀ (by positivity : 0<4096*(Real.exp 1)^2)).mp hchoose
    nlinarith only [hh]
  have hs : ‖mixedSourceSlope s v/mixedSourceSlope s y‖^2≤1/16 := by
    rw [mixedSourceSlope_ratio_sq hy0 hWy hWv]
    exact hr.trans hsmall
  nlinarith [norm_nonneg (mixedSourceSlope s v/mixedSourceSlope s y)]


theorem limitingAngularW_sub_one_norm (b θ : ℝ) :
    ‖(limitingAngularW b θ:ℂ)-1‖=|sectorDisplacement b θ| := by
  have he : (limitingAngularW b θ:ℂ)-1=((sectorDisplacement b θ:ℝ):ℂ) := by
    unfold limitingAngularW sectorDisplacement
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]

theorem mixed_slope_quarter_from_profiles {s : ℂ} {b θ φ v w outer inner t : ℝ}
    (hb : 0<Real.sin b) (hS : 0<1+Real.cos b) (ho : 0<outer) (hi : 0< inner)
    (hi1 : inner≤1) (his : inner≤(Real.sin b)^2/4)
    (hic : inner≤(Real.sin b)^2*outer*(1+Real.cos b)/(4096*(Real.exp 1)^2))
    (_hv : |v|≤1) (hw : |w|≤1) (hti : t≤ inner) (hto : t≤outer/4) (htS : t≤(1+Real.cos b)/2)
    (hprofilej : |sectorDisplacement b θ|≤ inner)
    (hprofileq : outer/2≤|sectorDisplacement b φ|)
    (hdj : ‖sourceW s (radialAnglePoint v θ)-(limitingAngularW b θ:ℂ)‖≤t)
    (hdq : ‖sourceW s (radialAnglePoint w φ)-(limitingAngularW b φ:ℂ)‖≤t)
    (hWj : 0<(sourceW s (radialAnglePoint v θ)).im)
    (hWq : 0<(sourceW s (radialAnglePoint w φ)).im) :
    ‖mixedSourceSlope s (radialAnglePoint w φ)/mixedSourceSlope s (radialAnglePoint v θ)‖≤1/4 := by
  have hnJ : Real.sin b≤‖radialAnglePoint v θ-(radialAnglePoint v θ)⁻¹‖ := by
    have hh := sector_inner_sine_lower hb hi.le his hprofilej
    exact (show Real.sin b≤2*|Real.sin θ| by linarith).trans (radialAnglePoint_difference_lower v θ)
  have hj : ‖sourceW s (radialAnglePoint v θ)-1‖≤2*inner := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (sourceW s (radialAnglePoint v θ)) (limitingAngularW b θ:ℂ) 1
    rw [limitingAngularW_sub_one_norm] at hh
    linarith
  have hq : outer/4≤‖sourceW s (radialAnglePoint w φ)-1‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (limitingAngularW b φ:ℂ) (sourceW s (radialAnglePoint w φ)) 1
    rw [limitingAngularW_sub_one_norm,norm_sub_rev (limitingAngularW b φ:ℂ)] at hh
    linarith
  have hqplus : (1+Real.cos b)/2≤‖sourceW s (radialAnglePoint w φ)+1‖ := by
    have hbase : 1+Real.cos b ≤ ‖(limitingAngularW b φ:ℂ)+1‖ := by
      have hreal : (limitingAngularW b φ:ℂ)+1=((limitingAngularW b φ+1:ℝ):ℂ) := by push_cast; rfl
      rw [hreal,Complex.norm_real,Real.norm_eq_abs]
      exact (show 1+Real.cos b≤limitingAngularW b φ+1 by unfold limitingAngularW; linarith [Real.cos_le_one φ]).trans (le_abs_self _)
    have hh := norm_sub_norm_le ((limitingAngularW b φ:ℂ)+1) (sourceW s (radialAnglePoint w φ)+1)
    rw [add_sub_add_right_eq_sub,norm_sub_rev] at hh
    linarith
  exact mixed_slope_quarter_of_trace_gaps hb ho hi hi1 hS hic hnJ
    (radialAnglePoint_difference_upper hw φ) hj hq hqplus hWj hWq

theorem mixedSourceSlope_ne_of_numerator {s y : ℂ} (hy : y-y⁻¹≠0)
    (hW : 0<(sourceW s y).im) : mixedSourceSlope s y≠0 := by
  exact div_ne_zero (mul_ne_zero Complex.I_ne_zero hy) (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne hW))

theorem mixed_slope_difference_ne {a b : ℂ} (ha : a≠0) (h : ‖b/a‖≤1/4) : a-b≠0 := by
  intro he
  have hab : a=b := sub_eq_zero.mp he
  rw [← hab,div_self ha,norm_one] at h
  norm_num at h


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem mixed_actual_profile_slope_separation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (outer : ℝ) (ho : 0<outer) :
    ∃ inner c e t₀ : ℝ, 0< inner ∧ inner≤outer/4 ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ, 0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
        |sectorDisplacement d.thetaB (θ j)|≤ inner → outer/2≤|sectorDisplacement d.thetaB (θ q)| →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        mixedSourceSlope s (y j)≠0 ∧ ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 ∧
          mixedSourceSlope s (y j)-mixedSourceSlope s (y q)≠0 := by
  have hb : 0<Real.sin d.thetaB := d.a_pos
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨c,eG,hc,hc1,heG,_heG1,hmargin⟩ := original_disk_trace_margin d.theta d.c₀ hsint d.c₀_pos hcsmall
  let inner := min (outer/4) (min 1 (min ((Real.sin d.thetaB)^2/4)
    ((Real.sin d.thetaB)^2*outer*(1+Real.cos d.thetaB)/(4096*(Real.exp 1)^2))))
  have hi : 0< inner := by dsimp [inner]; positivity
  have hio : inner≤outer/4 := min_le_left _ _
  have hi1 : inner≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hic : inner≤(Real.sin d.thetaB)^2*outer*(1+Real.cos d.thetaB)/(4096*(Real.exp 1)^2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let t := min inner (min (outer/4) ((1+Real.cos d.thetaB)/2))
  have ht : 0<t := lt_min hi (lt_min (by positivity) (by positivity))
  let e := min eG (min 1 (min (1/(4*(d.c₀+1))) (t/(8*(d.c₀+2)))))
  let t₀ := min (1/8:ℝ) (t/16)
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  have ht₀ : 0<t₀ := lt_min (by norm_num) (by positivity)
  refine ⟨inner,c,e,t₀,hi,hio,hc,he,ht₀,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j q s hN heps hepslt hτ hl0 hl1 htl hj hq hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let ρ := occupancy (fun i => f.p (θ i))/(N:ℝ)
  let v := fun i : Fin N => coupledRadialExponent d.c₀ eps (lam*τ) 1 (f.p (θ i)) (f.m (θ i)) ρ
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hρ0 : 0≤ρ := div_nonneg (occupancy_nonneg (fun i => (thresholdStep_range _ _ _).1)) hn.le
  have hρ1 : ρ≤1 := (div_le_one hn).mpr (occupancy_le (fun i => (thresholdStep_range _ _ _).2))
  have heG' := hepslt.trans_le (min_le_left eG _)
  have heps1 : eps≤1 := hepslt.le.trans ((min_le_right eG _).trans (min_le_left _ _))
  have hepbase : eps≤1/(4*(d.c₀+1)) := hepslt.le.trans
    ((min_le_right eG _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hept : eps≤t/(8*(d.c₀+2)) := hepslt.le.trans
    ((min_le_right eG _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hte : lam*τ≤1/8 := htl.le.trans (min_le_left _ _)
  have htt : lam*τ≤t/16 := htl.le.trans (min_le_right _ _)
  have hsmall : d.c₀*eps+2*(lam*τ)≤1 := by
    have hh := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<4*(d.c₀+1))).mp hepbase
    nlinarith
  have hyv (i : Fin N) : y i=radialAnglePoint (v i) (θ i) := by
    dsimp [y]
    rw [deformedPoint_scale_lambda,deformedPoint_coupledRadialExponent]
  have hv (i : Fin N) : |v i|≤1 := by
    have hh := coupledRadialExponent_bound (p := f.p (θ i)) (m := f.m (θ i)) d.c₀_pos.le heps.le (mul_nonneg hl0 hτ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
      (thresholdStep_range _ _ _).1 (thresholdStep_range _ _ _).2
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _) hρ0 hρ1
    exact hh.trans hsmall
  have hd (i : Fin N) : ‖sourceW s (y i)-(limitingAngularW d.thetaB (θ i):ℂ)‖≤t := by
    have hh := actual_deformed_sourceW_small_disk_motion d hN f heps.le heps1 (mul_nonneg hl0 hτ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
      (show c*eps≤1/4 by nlinarith)
      (fun x => thresholdStep_range _ _ _) (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
      hsmall θ i hs
    rw [← deformedPoint_scale_lambda] at hh
    have het := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<8*(d.c₀+2))).mp hept
    have hce := mul_le_mul_of_nonneg_right hc1 heps.le
    exact hh.trans (by nlinarith)
  have hm : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps)<(sourceS s).im := by
    simpa only [neg_mul,Real.exp_neg,inv_inv] using hmargin eps heps heG' s hs
  have hr : 0<Real.exp (-d.c₀*eps) := Real.exp_pos _
  have hr1 : Real.exp (-d.c₀*eps)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hphys (i : Fin N) : 0<(sourceW s (y i)).im := by
    have hh := sourceW_upper_of_margin hr hr1 hm (deformedPoint_zero_norm f hr.le τ θ i)
    exact hh.trans_le (deformed_sourceW_im_ge (by omega) f hr hτ hl0 θ s
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.nonneg _)
      (fun x hx => thresholdStep_zero (by linarith) (by linarith))
      (fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x hb hη hηsmall hx) i)
  have hratio : ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 := by
    rw [hyv j,hyv q]
    apply mixed_slope_quarter_from_profiles hb hS ho hi hi1 his hic (hv j) (hv q)
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) hj hq
    · simpa only [← hyv] using hd j
    · simpa only [← hyv] using hd q
    · simpa only [← hyv] using hphys j
    · simpa only [← hyv] using hphys q
  have hnon : mixedSourceSlope s (y j)≠0 := by
    apply mixedSourceSlope_ne_of_numerator _ (hphys j)
    apply norm_pos_iff.mp
    rw [hyv j]
    have hsin := sector_inner_sine_lower hb hi.le his hj
    exact (show 0<2*|Real.sin (θ j)| by linarith).trans_le (radialAnglePoint_difference_lower _ _)
  exact ⟨hnon,hratio,mixed_slope_difference_ne hnon hratio⟩


/-- The profiles are supplied by the actual nested partition and ALL finite
angular cutoff jets, rather than by a caller's population assignment. -/
theorem mixed_actual_nested_slope_separation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (outer : ℝ) (ho : 0<outer) :
    ∃ (inner : ℝ) (hi : 0< inner) (c e t₀ : ℝ), inner≤outer/4 ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ, 0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → sigma j=2 →
        θ ∈ tsupport (IsingBulk.Jets.cutoffJet l (nestedSectorWeight d.thetaB outer inner ho hi q sigma)) →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        mixedSourceSlope s (y j)≠0 ∧ ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 ∧
          mixedSourceSlope s (y j)-mixedSourceSlope s (y q)≠0 := by
  obtain ⟨inner,c,e,t₀,hi,hio,hc,he,ht,hbound⟩ := mixed_actual_profile_slope_separation d hcsmall outer ho
  refine ⟨inner,hi,c,e,t₀,hio,hc,he,ht,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hσ hsupport hs
  obtain ⟨hanchor,hassignment⟩ := nested_sector_jet_support d.thetaB outer inner ho hi q sigma l hsupport
  have houter := sectorOuterAnchor_tsupport d.thetaB outer ho q hanchor
  have hbranch := sector_assignment_tsupport d.thetaB inner hi sigma hassignment j
  have hj : |sectorDisplacement d.thetaB (θ j)|≤ inner := by
    rw [hσ] at hbranch
    have hefun : sectorLabel d.thetaB inner hi (2:Fin 3)=sectorBranch d.thetaB inner hi := by
      funext x
      simp [sectorLabel]
    rw [hefun] at hbranch
    have hb : θ j ∈ tsupport (sectorBranch d.thetaB inner hi) := hbranch
    exact (sector_labels_tsupport d.thetaB inner hi).2.2 hb
  exact hbound η α hη hηsmall hα N eps τ lam θ j q s hN heps hepslt hτ hl0 hl1 htl hj houter hs


theorem named_current_outer_profile {b α θ : ℝ} (_hb : 0<Real.sin b) (hα : 0<α)
    (hαsmall : α<Real.sin b/4) (hslo : α≤Real.sin θ) (hshi : Real.sin θ≤3*α/2) :
    (Real.sin b)^2/4 ≤ |sectorDisplacement b θ| := by
  have hsin0 : 0≤Real.sin θ := hα.le.trans hslo
  have hsinbd : Real.sin θ≤3*Real.sin b/8 := by linarith
  have hsum : |Real.cos θ+Real.cos b|≤2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one θ,Real.abs_cos_le_one b])
  have hd : (Real.cos θ)^2-(Real.cos b)^2≤2*|sectorDisplacement b θ| := by
    apply (le_abs_self _).trans
    rw [sq_sub_sq,abs_mul]
    have hh := mul_le_mul_of_nonneg_right hsum (abs_nonneg (Real.cos θ-Real.cos b))
    simpa only [sectorDisplacement,abs_sub_comm,mul_comm] using hh
  have hs := pow_le_pow_left₀ hsin0 hsinbd 2
  have ht := Real.sin_sq_add_cos_sq θ
  have htb := Real.sin_sq_add_cos_sq b
  nlinarith

/-- Named Stokes anchors already have a fixed outer profile separation.
The optional cap permits a further inner shrink to the actual m=1 plateau. -/
theorem mixed_actual_current_slope_separation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) :
    ∃ inner c e t₀ : ℝ, 0< inner ∧ inner≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ, 0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
        |sectorDisplacement d.thetaB (θ j)|≤ inner →
        θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        mixedSourceSlope s (y j)≠0 ∧ ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 ∧
          mixedSourceSlope s (y j)-mixedSourceSlope s (y q)≠0 := by
  let outer := (Real.sin d.thetaB)^2/2
  have ho : 0<outer := by dsimp [outer]; positivity [d.a_pos]
  obtain ⟨inner,c,e,t₀,hi,_hio,hc,he,ht,hbound⟩ := mixed_actual_profile_slope_separation d hcsmall outer ho
  refine ⟨min inner cap,c,e,t₀,lt_min hi hcap,min_le_right _ _,hc,he,ht,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j q s hN heps hepslt hτ hl0 hl1 htl hj hsupport hs
  obtain ⟨_,_,hlo,hall,_⟩ := constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα q hsupport
  have hq : outer/2≤|sectorDisplacement d.thetaB (θ q)| := by
    have hh := named_current_outer_profile d.a_pos hα hαsmall hlo (hall q)
    simpa only [outer,div_div,show (2:ℝ)*2=4 by norm_num] using hh
  exact hbound η α hη hηsmall hα N eps τ lam θ j q s hN heps hepslt hτ hl0 hl1 htl
    (hj.trans (min_le_left _ _)) hq hs


end
end IsingBulk.Tail
