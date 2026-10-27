import IsingBulk.Preferred22.IntegratedCoarea
import IsingBulk.Preferred22.OneBodyScale

/-! The actual negative-minimum physical estimate preceding q26. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

def preferredBranchPlateauWidth (d : PreferredBranchData) (B : PreferredCoareaBump d) : ℝ :=
  min ((Real.pi-B.delta-d.b)/2) ((d.b-B.delta)/2)

theorem preferredBranchPlateauWidth_pos (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    0 < preferredBranchPlateauWidth d B := by
  unfold preferredBranchPlateauWidth
  apply lt_min <;> linarith [B.branch_plateau,B.delta_b,d.b_pos]

theorem preferred_branch_plateau_of_abs (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {u : ℝ} (hu : |u| < preferredBranchPlateauWidth d B) :
    -d.b+u ∈ Ioo (-(Real.pi-B.delta)) (-B.delta) := by
  have h₁ := hu.trans_le (min_le_left _ _)
  have h₂ := hu.trans_le (min_le_right _ _)
  have hlo := (abs_lt.mp h₁).1
  have hhi := (abs_lt.mp h₂).2
  constructor <;> linarith [abs_nonneg u,B.branch_plateau,B.delta_b,d.b_pos]

theorem preferred_actual_plateau_angle (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ σ υ : ℝ) {u : ℝ} (hu : |u| < preferredBranchPlateauWidth d B) :
    preferredBumpAngle B.m B.p τ σ υ (-d.b+u) = outwardPlateauAngle d (τ*σ) u := by
  obtain ⟨hp,hm,_⟩ := B.lower_plateau_jets (preferred_branch_plateau_of_abs d B hu)
  unfold preferredBumpAngle outwardPlateauAngle
  rw [hp,hm]
  push_cast
  ring

theorem preferred_actual_plateau_phase (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ : ℝ) {u : ℝ} (hu : |u| < preferredBranchPlateauWidth d B) :
    preferredAngularPhase d ε (preferredBumpAngle B.m B.p τ σ υ (-d.b+u)) =
      outwardPlateauPhase d ε (τ*σ) u := by
  rw [preferred_actual_plateau_angle d B τ σ υ hu]
  unfold preferredAngularPhase outwardPlateauPhase
  rw [outwardPlateauW_formula]
  rfl

theorem preferred_actual_plateau_slope (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ : ℝ) {u : ℝ} (hu : |u| < preferredBranchPlateauWidth d B) :
    preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u) =
      -Complex.sin (outwardPlateauAngle d (τ*σ) u)/
        Complex.sin (outwardPlateauPhase d ε (τ*σ) u) := by
  unfold preferredCompactSlope
  rw [preferred_actual_plateau_angle d B τ σ υ hu]
  unfold preferredPhaseSlope outwardPlateauPhase
  rw [outwardPlateauW_formula]
  rfl

set_option maxHeartbeats 900000 in
/-- The complete right-rectangle one-body Jacobian envelope, together with
its genuinely physical negative-side square-root attenuation. Constants are
fixed before occupancies and before particle number. -/
theorem preferred_full_right_onebody_and_attenuation (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A c ε₀ τ₀ δB : ℝ, 0 < A ∧ 0 < c ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
      0 < δB ∧ δB < B.delta ∧ δB < 1 ∧ ε₀ ≤ 1 ∧ τ₀ ≤ 1 ∧
      ∀ ε τ σ υ u : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → -δB ≤ u → u ≤ d.b+B.delta →
      ‖preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u)+1‖ ≤
        A/Real.sqrt (|u|+ε) ∧
      (u ≤ 0 → c*Real.sqrt (|u|+ε) ≤
        -(preferredAngularPhase d ε (preferredBumpAngle B.m B.p τ σ υ (-d.b+u))).im) := by
  obtain ⟨_,Cs,εs,τs,_,hCs,hεs,hτs,hs⟩ := preferred_full_right_projection d B
  obtain ⟨_,Cb,rb,_,hCb,hrb,hb⟩ := preferred_outward_phase_derivative_size d
  obtain ⟨rd,hrd,hd⟩ := preferred_outward_branch_domain d
  obtain ⟨c,ra,hc,hra,ha⟩ := preferred_outward_negative_attenuation d
  let r := min rb (min rd ra)
  have hr : 0 < r := lt_min hrb (lt_min hrd hra)
  have hrrb : r ≤ rb := min_le_left _ _
  have hrrd : r ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hrra : r ≤ ra := (min_le_right _ _).trans (min_le_right _ _)
  let δB := min (1/2) (min (B.delta/2) (min (preferredBranchPlateauWidth d B/2) (r/2)))
  have hδB : 0 < δB := by dsimp [δB]; positivity [preferredBranchPlateauWidth_pos d B,B.delta_pos]
  have hδB1 : δB < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδBδ : δB < B.delta := by
    have h : δB ≤ B.delta/2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [B.delta_pos]
  have hδBw : δB < preferredBranchPlateauWidth d B := by
    have h : δB ≤ preferredBranchPlateauWidth d B/2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith [preferredBranchPlateauWidth_pos d B]
  have hδBr : δB < r := by
    have h : δB ≤ r/2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let ε₀ := min 1 (min εs r)
  let τ₀ := min 1 (min τs r)
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  let R := d.b+B.delta+3
  have hR : 0 < R := by dsimp [R]; have := d.b_pos; have := B.delta_pos; positivity
  let A₀ := max Cs Cb
  have hA₀ : 0 < A₀ := hCs.trans_le (le_max_left _ _)
  let A := A₀+Real.sqrt R
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,c,ε₀,τ₀,δB,hA,hc,hε₀,hτ₀,hδB,hδBδ,hδB1,min_le_left _ _,min_le_left _ _,?_⟩
  intro ε τ σ υ u hε hεr hτ hτr hσ hυ hul hur
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hεs' : ε < εs := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεr' : ε < r := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτs' : τ < τs := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτr' : τ < r := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0 ≤ τ*σ := mul_nonneg hτ hσ.1
  have hδr : τ*σ < r := (mul_le_of_le_one_right hτ hσ.2).trans_lt hτr'
  have hL : 0 < |u|+ε := by positivity
  have hLR : |u|+ε ≤ R := by
    have habs : |u| ≤ d.b+B.delta+1 := by
      rw [abs_le]
      constructor <;> linarith [d.b_pos,B.delta_pos]
    dsimp [R]
    linarith
  have hraw : ‖preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u)‖ ≤ A₀/Real.sqrt (|u|+ε) := by
    by_cases hu : 0 ≤ u
    · have hh := (hs ε τ σ υ u hε hεs' hτ hτs' hσ hυ hu hur).2
      rw [abs_of_nonneg hu]
      exact hh.trans (div_le_div₀ (le_of_lt hA₀) (le_max_left _ _)
        (Real.sqrt_pos.mpr (by positivity : 0 < u+ε))
        (Real.sqrt_le_sqrt (by linarith)))
    · have hu0 : u ≤ 0 := (lt_of_not_ge hu).le
      have huabs : |u| < r := by rw [abs_of_nonpos hu0]; linarith
      have huw : |u| < preferredBranchPlateauWidth d B := by rw [abs_of_nonpos hu0]; linarith
      obtain ⟨hre,him⟩ := hd ε (τ*σ) u hε (hεr'.trans_le hrrd) hδ
        (hδr.trans_le hrrd) (huabs.trans_le hrrd)
      have hh := (hb ε (τ*σ) u hε (hεr'.trans_le hrrb) hδ
        (hδr.trans_le hrrb) (huabs.trans_le hrrb)).2
      rw [(outwardPlateauPhase_hasDerivAt d ε (τ*σ) u hre him).deriv] at hh
      rw [preferred_actual_plateau_slope d B ε τ σ υ huw]
      exact hh.trans (div_le_div₀ hA₀.le (le_max_right _ _)
        (Real.sqrt_pos.mpr hL) (Real.sqrt_le_sqrt (by linarith)))
  refine ⟨shifted_slope_bound hL hLR hraw,?_⟩
  intro hu0
  have huabs : |u| < r := by rw [abs_of_nonpos hu0]; linarith
  have huw : |u| < preferredBranchPlateauWidth d B := by rw [abs_of_nonpos hu0]; linarith
  rw [preferred_actual_plateau_phase d B ε τ σ υ huw]
  have hh := ha ε (τ*σ) u hε (hεr'.trans_le hrra) hδ (hδr.trans_le hrra) hu0
    (huabs.trans_le hrra)
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : |u|+ε ≤ |u|+ε+τ*σ)) hc.le).trans hh

/-- The attenuation of any one actual physical root is bounded by the
complete product attenuation. This uses the physical upper-W sheet of every
factor, and remains valid on the enlarged full angular rectangle. -/
theorem preferred_single_phase_attenuation_le_total {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (θ : Fin N → ℝ) (i : Fin N) :
    -(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im ≤
      -(preferredTotalPhase d ε τ B.p B.m θ).im := by
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hpos (v : Fin N) : 0 ≤ -(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ v)).im := by
    have hW := (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ v)
    exact (neg_pos.mpr (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2.2.2).le
  have h := Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) => hpos v) (Finset.mem_univ i)
  have he : (preferredTotalPhase d ε τ B.p B.m θ).im =
      ∑ v, (preferredAngularPhase d ε (deformedAngles τ B.p B.m θ v)).im :=
    map_sum Complex.imCLM _ _
  rw [he]
  simpa only [Finset.sum_neg_distrib] using h

set_option maxHeartbeats 900000 in
/-- Literal physical negative-minimum majorant preceding q26. Both actual
one-body Jacobian factors remain present and the product denominator uses all
particles. No positive lower bound on diameter or epsilon is imposed. -/
theorem preferred_actual_negative_pair_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ K ε₀ τ₀ δB : ℝ, 0 < K ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ, (∀ v, θ v ∈ Icc (-d.b-δB) B.delta) →
      ∀ i j : Fin N, θ i+d.b ≤ 0 →
      preferredExtremePair d B ε τ θ i j/‖1-preferredActualZ d B ε τ θ‖ ≤
        K/((|θ i+d.b|+ε)*Real.sqrt (|θ j+d.b|+ε)) := by
  obtain ⟨A,c,ε₀,τ₀,δB,hA,hc,hε₀,hτ₀,hδB,hδBδ,hδB1,hε01,_,hsource⟩ :=
    preferred_full_right_onebody_and_attenuation d B
  let c₀ := min c (1/2)
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  let C₀ := obliqueKernelConstant 1 0
  have hC₀ : 0 < C₀ := by
    exact lt_of_lt_of_le (by positivity : 0 < (1+|(0:ℝ)|)*Real.exp 1+1*Real.pi)
      (le_max_left _ _)
  let K := A^2*C₀/c₀
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,ε₀,τ₀,δB,hK,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ i j hi
  let σ := occupancy B.p θ/(N:ℝ)
  let υ := occupancy B.m θ/(N:ℝ)
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  let a := |θ i+d.b|+ε
  let b := |θ j+d.b|+ε
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have ha2 : a ≤ 2 := by dsimp [a]; rw [abs_of_nonpos hi]; linarith [(hθ i).1,hεr.trans_le hε01]
  have hsqrta : Real.sqrt a ≤ 2 := by nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg a]
  have hsrc (v : Fin N) := hsource ε τ σ υ (θ v+d.b) hε hεr hτ hτr hσ hυ
    (by linarith [(hθ v).1]) (by linarith [(hθ v).2])
  have hfactor (v : Fin N) : ‖actualBumpSlopeVector d B ε τ θ v+1‖ ≤
      A/Real.sqrt (|θ v+d.b|+ε) := by
    simpa only [actualBumpSlopeVector,σ,υ,show -d.b+(θ v+d.b)=θ v by ring] using (hsrc v).1
  have hnum : preferredExtremePair d B ε τ θ i j ≤ A^2/(Real.sqrt a*Real.sqrt b) := by
    unfold preferredExtremePair
    rw [norm_mul]
    calc
      _ ≤ (A/Real.sqrt a)*(A/Real.sqrt b) := mul_le_mul (hfactor i) (hfactor j) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hlocal : c*Real.sqrt a ≤ -(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im := by
    rw [actual_bump_angle]
    simpa only [σ,υ,a,show -d.b+(θ i+d.b)=θ i by ring] using (hsrc i).2 hi
  let G := preferredTotalPhase d ε τ B.p B.m θ
  have hfloor : c₀*Real.sqrt a ≤ -G.im :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg a)).trans
      (hlocal.trans (preferred_single_phase_attenuation_le_total d B hε hτ θ i))
  have hfloor0 : 0 < c₀*Real.sqrt a := mul_pos hc₀ (Real.sqrt_pos.mpr ha)
  have hfloor1 : c₀*Real.sqrt a ≤ 1 := by
    have hc₀half : c₀ ≤ 1/2 := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hc₀half (Real.sqrt_nonneg a)]
  have he : (G.re:ℂ)-Complex.I*((-G.im:ℝ):ℂ)=G := by apply Complex.ext <;> simp
  have hk := actual_oblique_periodic_kernel (x := G.re) (a := -G.im) (θ := 0)
    (by simp [Real.pi_pos]) hfloor0 hfloor1 hfloor
  rw [he,← preferredActualZ_eq_exp d B hε hτ θ] at hk
  simp only [Real.cos_zero,Real.sin_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul] at hk
  have hden : ‖1-preferredActualZ d B ε τ θ‖⁻¹ ≤ C₀/(c₀*Real.sqrt a) := by
    exact hk.trans (div_le_div_of_nonneg_left hC₀.le hfloor0
      (by linarith [projectedDistance_nonneg 1 G.re]))
  calc
    preferredExtremePair d B ε τ θ i j/‖1-preferredActualZ d B ε τ θ‖ =
        preferredExtremePair d B ε τ θ i j*‖1-preferredActualZ d B ε τ θ‖⁻¹ := div_eq_mul_inv _ _
    _ ≤ (A^2/(Real.sqrt a*Real.sqrt b))*(C₀/(c₀*Real.sqrt a)) :=
      mul_le_mul hnum hden (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = K/(a*Real.sqrt b) := by
      dsimp [K]
      field_simp
      nlinarith [Real.sq_sqrt ha.le]
    _ = _ := rfl

set_option maxHeartbeats 1000000 in
/-- Actual q27 on the negative-minimum part of a geometric extreme interval.
The reciprocal majorants are integrated on the literal affine constrained
coordinates, not on a postulated finite collection of cutoff fibers. -/
theorem preferred_negative_extreme_integral (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N, ∀ x y r T : ℝ,
      x ≤ y → 0 < r → r ≤ T →
      (∀ t ∈ Icc x y,
        (∀ v, extremeAnglePath θ i j t v ∈ Icc (-d.b-δB) B.delta) ∧
        extremeAnglePath θ i j t i+d.b ≤ 0 ∧
        r ≤ extremeAnglePath θ i j t j-extremeAnglePath θ i j t i) →
      (∫ t : ℝ in x..y,
        preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
          ‖1-preferredActualZ d B ε τ (extremeAnglePath θ i j t)‖) ≤
        C*Real.sqrt T/r*(1+|Real.log ε|) := by
  obtain ⟨K,εp,τp,δB,hK,hεp,hτp,hδB,hδBδ,hpair⟩ := preferred_actual_negative_pair_bound d B
  obtain ⟨cp,Cp,hcp,_,hphase⟩ := preferred_actual_phase_control d B
  let ε₀ := min 1 εp
  let τ₀ := min 1 τp
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) hεp
  have hτ₀ : 0 < τ₀ := lt_min (by norm_num) hτp
  let R := d.b+B.delta+2
  have hR : 0 < R := by dsimp [R]; have := d.b_pos; have := B.delta_pos; positivity
  let L := 2*(1+|Real.log (R+1)|)
  have hL : 0 < L := by dsimp [L]; positivity
  let C := 2*K*L
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ i j x y r T hxy hr hrT hgeom
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hεp' : ε < εp := hεr.trans_le (min_le_right _ _)
  have hτ1 : τ ≤ 1 := (hτr.trans_le (min_le_left _ _)).le
  have hτp' : τ < τp := hτr.trans_le (min_le_right _ _)
  have hij : i ≠ j := by
    intro he
    have hh := (hgeom x (left_mem_Icc.mpr hxy)).2.2
    rw [he,sub_self] at hh
    linarith
  have hei (t : ℝ) : extremeAnglePath θ i j t i+d.b = (θ i+d.b)+t := by
    simp only [extremeAnglePath,ite_true,ite_eq_right hij]
    ring
  have hej (t : ℝ) : extremeAnglePath θ i j t j+d.b = (θ j+d.b)-t := by
    simp only [extremeAnglePath,ite_true,ite_eq_right hij.symm]
    ring
  let G := fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)
  let F := fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j
  let Z := fun t : ℝ => preferredActualZ d B ε τ (extremeAnglePath θ i j t)
  let fi := fun t : ℝ => preferredReciprocalMajorant ε ((θ i+d.b)+t)
  let fj := fun t : ℝ => preferredReciprocalMajorant ε ((θ j+d.b)-t)
  have hfi : Continuous fi := (preferredReciprocalMajorant_continuous hε).comp (by fun_prop)
  have hfj : Continuous fj := (preferredReciprocalMajorant_continuous hε).comp (by fun_prop)
  have hF : Continuous F :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hG : Continuous G := (preferred_extreme_phase_smooth d B hε hτ θ i j).continuous
  have hZ : Continuous Z := by
    have he : Z = fun t : ℝ => Complex.exp (-Complex.I*G t) := by
      funext t
      exact preferredActualZ_eq_exp d B hε hτ _
    rw [he]
    fun_prop
  have hden (t : ℝ) : ‖1-Z t‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    change 1-preferredActualZ d B ε τ (extremeAnglePath θ i j t) ≠ 0
    rw [preferredActualZ_eq_exp d B hε hτ]
    apply preferred_phase_denominator_ne_zero
    have hh := (hphase N hN ε τ hε hε1 hτ hτ1 (extremeAnglePath θ i j t)).1
    have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
    nlinarith only [hh,mul_pos (mul_pos hcp hNp) hε]
  have hleft : Continuous (fun t : ℝ => F t/‖1-Z t‖) :=
    hF.div ((continuous_const.sub hZ).norm) hden
  have hpt (t : ℝ) (ht : t ∈ Icc x y) :
      F t/‖1-Z t‖ ≤ (K/Real.sqrt r)*(fi t+fj t) := by
    obtain ⟨hbox,hneg,hdiam⟩ := hgeom t ht
    let a := |extremeAnglePath θ i j t i+d.b|+ε
    let b := |extremeAnglePath θ i j t j+d.b|+ε
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hab : r ≤ a+b := by
      dsimp [a,b]
      rw [abs_of_nonpos hneg]
      linarith [le_abs_self (extremeAnglePath θ i j t j+d.b)]
    have hh := hpair N hN ε τ hε hεp' hτ hτp' (extremeAnglePath θ i j t) hbox i j hneg
    have hq := negative_minimum_pair_bound ha hb hr hab
    calc
      F t/‖1-Z t‖ ≤ K/(a*Real.sqrt b) := hh
      _ = K*(1/(a*Real.sqrt b)) := by ring
      _ ≤ K*(1/Real.sqrt r*(1/a+1/b)) := mul_le_mul_of_nonneg_left hq hK.le
      _ = (K/Real.sqrt r)*(fi t+fj t) := by
        dsimp [a,b,fi,fj,preferredReciprocalMajorant]
        rw [hei,hej]
        ring
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hxy (hleft.intervalIntegrable x y)
    ((continuous_const.mul (hfi.add hfj)).intervalIntegrable x y) hpt
  have hboxR (t : ℝ) (ht : t ∈ Icc x y) (v : Fin N) :
      -R ≤ extremeAnglePath θ i j t v+d.b ∧ extremeAnglePath θ i j t v+d.b ≤ R := by
    have hb := (hgeom t ht).1 v
    dsimp [R]
    constructor <;> linarith [hb.1,hb.2,d.b_pos,B.delta_pos]
  have hii : (∫ t : ℝ in x..y, fi t) ≤ L*(1+|Real.log ε|) := by
    apply preferred_reciprocal_affine_add hε hε1 hR.le hxy
    · simpa only [hei] using (hboxR x (left_mem_Icc.mpr hxy) i).1
    · simpa only [hei] using (hboxR y (right_mem_Icc.mpr hxy) i).2
  have hji : (∫ t : ℝ in x..y, fj t) ≤ L*(1+|Real.log ε|) := by
    apply preferred_reciprocal_affine_sub hε hε1 hR.le hxy
    · simpa only [hej] using (hboxR x (left_mem_Icc.mpr hxy) j).2
    · simpa only [hej] using (hboxR y (right_mem_Icc.mpr hxy) j).1
  have hscale : 1/Real.sqrt r ≤ Real.sqrt T/r := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hr) hr).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrT) (Real.sqrt_nonneg r)
    nlinarith [Real.sq_sqrt hr.le]
  calc
    (∫ t : ℝ in x..y, F t/‖1-Z t‖) ≤ ∫ t : ℝ in x..y, (K/Real.sqrt r)*(fi t+fj t) := hmono
    _ = (K/Real.sqrt r)*((∫ t : ℝ in x..y, fi t)+(∫ t : ℝ in x..y, fj t)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hfi.intervalIntegrable x y) (hfj.intervalIntegrable x y)]
    _ ≤ (K/Real.sqrt r)*(2*L*(1+|Real.log ε|)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (2*K*L)*(1/Real.sqrt r)*(1+|Real.log ε|) := by ring
    _ ≤ (2*K*L)*(Real.sqrt T/r)*(1+|Real.log ε|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) (by positivity)
    _ = C*Real.sqrt T/r*(1+|Real.log ε|) := by dsimp [C]; ring

end
end IsingBulk.Preferred22
