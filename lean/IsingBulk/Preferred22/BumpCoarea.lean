import IsingBulk.Preferred22.Coarea
import IsingBulk.Preferred22.ContourLegality
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Preferred22: smooth bump and fixed-occupancy coarea bridge

This module glues the derived physical plateau estimates to the derived compact
right-arc estimates. Bump smoothness/support are source data; no complete coarea
or tail bound is supplied as a field.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter

theorem PreferredCoareaBump.m_smooth {d : PreferredBranchData}
    (B : PreferredCoareaBump d) : ContDiff ℝ ∞ B.m :=
  B.smooth.comp (contDiff_id.neg)

/-- The periodic bump has the manuscript's sine support property on the
whole angular line, obtained from its precise principal-interval support. -/
theorem PreferredCoareaBump.p_zero_of_sin_nonpos {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ : ℝ} (hθ : Real.sin θ ≤ 0) : B.p θ = 0 := by
  obtain ⟨n,hn⟩ := exists_period_representative (by positivity : 0 < 2*Real.pi) θ
  let t := θ-(n:ℝ)*(2*Real.pi)
  have ht : t ∈ Icc (-Real.pi) Real.pi := by
    have h : |t| ≤ Real.pi := by
      dsimp [t]
      nlinarith [hn]
    exact abs_le.mp h
  have hp : B.p t = B.p θ := by
    simpa only [t,zsmul_eq_mul] using B.periodic.sub_zsmul_eq (x := θ) n
  have hs : Real.sin t = Real.sin θ := by
    simpa only [t,zsmul_eq_mul] using Real.sin_periodic.sub_zsmul_eq (x := θ) n
  by_contra h
  have hpt : B.p t ≠ 0 := by rwa [hp]
  have hspos := Real.sin_pos_of_pos_of_lt_pi (B.upper_support t ht hpt).1
    (B.upper_support t ht hpt).2
  rw [hs] at hspos
  linarith

theorem PreferredCoareaBump.m_zero_of_sin_nonneg {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) : B.m θ = 0 := by
  exact B.p_zero_of_sin_nonpos (by simpa only [Real.sin_neg] using neg_nonpos.mpr hθ)

/-- On the actual lower branch plateau the bump values and their first two
real derivatives are exact constants. -/
theorem PreferredCoareaBump.lower_plateau_jets {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ : ℝ}
    (hθ : θ ∈ Ioo (-(Real.pi-B.delta)) (-B.delta)) :
    B.p θ = 0 ∧ B.m θ = 1 ∧ deriv B.p θ = 0 ∧ deriv B.m θ = 0 ∧
      deriv (deriv B.p) θ = 0 ∧ deriv (deriv B.m) θ = 0 := by
  let U := Ioo (-(Real.pi-B.delta)) (-B.delta)
  have hp0 (v : ℝ) (hv : v ∈ U) : B.p v = 0 := by
    by_contra h
    have hpv := B.upper_support v (by
      constructor <;> dsimp [U] at hv <;> linarith [B.delta_pos, hv.1, hv.2]) h
    dsimp [U] at hv
    linarith [hpv.1,hv.2,B.delta_pos]
  have hm1 (v : ℝ) (hv : v ∈ U) : B.m v = 1 := by
    apply B.plateau
    dsimp [U] at hv
    constructor <;> linarith [hv.1,hv.2]
  have hp1 (v : ℝ) (hv : v ∈ U) : deriv B.p v = 0 := by
    have he : B.p =ᶠ[𝓝 v] (fun _ => 0) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hv) (fun y hy => hp0 y hy)
    exact ((hasDerivAt_const v (0:ℝ)).congr_of_eventuallyEq he).deriv
  have hm1' (v : ℝ) (hv : v ∈ U) : deriv B.m v = 0 := by
    have he : B.m =ᶠ[𝓝 v] (fun _ => 1) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hv) (fun y hy => hm1 y hy)
    exact ((hasDerivAt_const v (1:ℝ)).congr_of_eventuallyEq he).deriv
  have hp2 (v : ℝ) (hv : v ∈ U) : deriv (deriv B.p) v = 0 := by
    have he : deriv B.p =ᶠ[𝓝 v] (fun _ => 0) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hv) (fun y hy => hp1 y hy)
    exact ((hasDerivAt_const v (0:ℝ)).congr_of_eventuallyEq he).deriv
  have hm2 (v : ℝ) (hv : v ∈ U) : deriv (deriv B.m) v = 0 := by
    have he : deriv B.m =ᶠ[𝓝 v] (fun _ => 0) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hv) (fun y hy => hm1' y hy)
    exact ((hasDerivAt_const v (0:ℝ)).congr_of_eventuallyEq he).deriv
  exact ⟨hp0 θ hθ,hm1 θ hθ,hp1 θ hθ,hm1' θ hθ,hp2 θ hθ,hm2 θ hθ⟩

theorem PreferredCoareaBump.near_lower_plateau {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {u : ℝ} (hu : 0 ≤ u) (hur : u < (d.b-B.delta)/2) :
    -d.b+u ∈ Ioo (-(Real.pi-B.delta)) (-B.delta) := by
  have hb := B.branch_plateau
  have hδ := B.delta_b
  have hbpos := d.b_pos
  constructor <;> linarith

/-- The full compact-source transported curvature agrees exactly with the
physical plateau curvature, because all real bump jets vanish there. -/
theorem preferredBump_curvature_plateau (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ u : ℝ) (hu : 0 ≤ u) (hur : u < (d.b-B.delta)/2) :
    preferredCompactTransportCurvature d B.m B.p (deriv B.m) (deriv B.p)
      (deriv (deriv B.m)) (deriv (deriv B.p)) ε τ σ υ (-d.b+u) =
        outwardCurvature d ε (τ*σ) u := by
  obtain ⟨hp,hm,hp',hm',hp'',hm''⟩ := B.lower_plateau_jets (B.near_lower_plateau hu hur)
  have hf : preferredBumpAngle B.m B.p τ σ υ (-d.b+u) =
      outwardPlateauAngle d (τ*σ) u := by
    unfold preferredBumpAngle outwardPlateauAngle
    rw [hp,hm]
    push_cast
    ring
  have ha : preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ (-d.b+u) = 1 := by
    simp [preferredBumpTangent,hp',hm']
  have ha' : preferredBumpSecond (deriv (deriv B.m)) (deriv (deriv B.p)) τ σ υ (-d.b+u) = 0 := by
    simp [preferredBumpSecond,hp'',hm'']
  unfold preferredCompactTransportCurvature
  rw [ha,ha']
  simp only [one_pow,mul_one,mul_zero,sub_zero]
  unfold preferredCompactCurvature
  rw [hf]
  unfold preferredPhaseCurvature outwardCurvature outwardCurvatureNumerator outwardPlateauPhase
  rw [outwardPlateauW_formula]
  rfl

/-- The same exact agreement for the one-body phase slope. -/
theorem preferredBump_slope_plateau (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ u : ℝ) (hu : 0 ≤ u) (hur : u < (d.b-B.delta)/2) :
    preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u) =
      -Complex.sin (outwardPlateauAngle d (τ*σ) u)/
        Complex.sin (outwardPlateauPhase d ε (τ*σ) u) := by
  obtain ⟨hp,hm,_⟩ := B.lower_plateau_jets (B.near_lower_plateau hu hur)
  have hf : preferredBumpAngle B.m B.p τ σ υ (-d.b+u) =
      outwardPlateauAngle d (τ*σ) u := by
    unfold preferredBumpAngle outwardPlateauAngle
    rw [hp,hm]
    push_cast
    ring
  unfold preferredCompactSlope
  rw [hf]
  unfold preferredPhaseSlope outwardPlateauPhase
  rw [outwardPlateauW_formula]
  rfl


/-- The complete fixed-occupancy right interval: the true-branch plateau
and compact transition estimates are glued with constants fixed before the
occupancy parameters. The field is the full −B'=Q*a²−b*a' and the bumps are
only C-infinity on the real line. -/
theorem preferred_full_right_projection (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c C ε0 τ0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε0 ∧ 0 < τ0 ∧
      ∀ ε τ σ υ u : ℝ, 0 < ε → ε < ε0 → 0 ≤ τ → τ < τ0 →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → 0 ≤ u → u ≤ d.b+B.delta →
      c*(u+ε+τ*σ)^(-(3/2:ℝ)) ≤
        preferredCompactProjectedCurvature d B.m B.p (deriv B.m) (deriv B.p)
          (deriv (deriv B.m)) (deriv (deriv B.p)) ε τ σ υ (-d.b+u) ∧
      ‖preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u)‖ ≤
        C/Real.sqrt (u+ε+τ*σ) := by
  obtain ⟨c₁,_,r₁,hc₁,_,hr₁,hcurve⟩ := preferred_outward_curvature_scale d
  obtain ⟨_,C₁,r₂,_,hC₁,hr₂,hslope⟩ := preferred_outward_phase_derivative_size d
  obtain ⟨r₃,hr₃,hdomain⟩ := preferred_outward_branch_domain d
  let r₀ := min r₁ (min r₂ r₃)
  have hr₀ : 0 < r₀ := lt_min hr₁ (lt_min hr₂ hr₃)
  have hr01 : r₀ ≤ r₁ := min_le_left _ _
  have hr02 : r₀ ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr03 : r₀ ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hbδ : 0 < d.b-B.delta := by linarith [B.delta_b,d.b_pos]
  let ρ := min ((d.b-B.delta)/4) (r₀/2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρB : ρ < (d.b-B.delta)/2 := by
    have := min_le_left ((d.b-B.delta)/4) (r₀/2)
    dsimp [ρ]
    linarith
  have hρr : ρ < r₀ := by
    have := min_le_right ((d.b-B.delta)/4) (r₀/2)
    dsimp [ρ]
    linarith
  have hpm : ContDiff ℝ ∞ (deriv B.p) := (contDiff_infty_iff_deriv.mp B.smooth).2
  have hmm : ContDiff ℝ ∞ (deriv B.m) := (contDiff_infty_iff_deriv.mp B.m_smooth).2
  obtain ⟨a,C₂,r₄,ha,hC₂,hr₄,hcompact⟩ :=
    preferred_compact_right_transport_curvature d B.m B.p (deriv B.m) (deriv B.p)
      (deriv (deriv B.m)) (deriv (deriv B.p)) B.m_smooth.continuous B.smooth.continuous
      hmm.continuous hpm.continuous
      (hmm.continuous_deriv (by simp)) (hpm.continuous_deriv (by simp))
      hρ (by linarith [B.delta_b,d.b_pos] : B.delta < d.b)
  let k₁ := Real.cos (3*Real.pi/8)/108*c₁
  have hk₁ : 0 < k₁ := by dsimp [k₁]; have := preferred_oblique_angle_margin.1; positivity
  let k := min k₁ (a*ρ^(3/2:ℝ))
  have hk : 0 < k := lt_min hk₁ (mul_pos ha (Real.rpow_pos_of_pos hρ _))
  let R := d.b+B.delta+2
  have hR : 0 < R := by dsimp [R]; have := d.b_pos; have := B.delta_pos; positivity
  let C := max C₁ (C₂*Real.sqrt R)
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  let η := min 1 (min r₀ r₄)
  have hη : 0 < η := lt_min (by norm_num) (lt_min hr₀ hr₄)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη0 : η ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η ≤ r₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨k,C,η,η,hk,hC,hη,hη,?_⟩
  intro ε τ σ υ u hε hεr hτ hτr hσ hυ hu huR
  have hδ : 0 ≤ τ*σ := mul_nonneg hτ hσ.1
  have hδτ : τ*σ ≤ τ := by nlinarith [mul_le_mul_of_nonneg_left hσ.2 hτ]
  have hδr : τ*σ < r₀ := hδτ.trans_lt (hτr.trans_le hη0)
  have hε0 : ε < r₀ := hεr.trans_le hη0
  let L := u+ε+τ*σ
  have hL : 0 < L := by dsimp [L]; positivity
  have hLR : L ≤ R := by
    dsimp [L,R]
    linarith [hεr.trans_le hη1,hτr.trans_le hη1]
  by_cases hur : u < ρ
  · have huB := hur.trans hρB
    have hur₀ := hur.trans hρr
    have hprojection :
        preferredCompactProjectedCurvature d B.m B.p (deriv B.m) (deriv B.p)
          (deriv (deriv B.m)) (deriv (deriv B.p)) ε τ σ υ (-d.b+u) =
        (Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))*outwardCurvature d ε (τ*σ) u).re := by
      unfold preferredCompactProjectedCurvature
      rw [preferredBump_curvature_plateau d B ε τ σ υ u hu huB]
      rfl
    have hcv := (hcurve ε (τ*σ) u hε (hε0.trans_le hr01) hδ (hδr.trans_le hr01)
      hu (hur₀.trans_le hr01)).2.2
    obtain ⟨hwr,hwi⟩ := hdomain ε (τ*σ) u hε (hε0.trans_le hr03) hδ (hδr.trans_le hr03)
      (by simpa only [abs_of_nonneg hu] using hur₀.trans_le hr03)
    have hder := (outwardPlateauPhase_hasDerivAt d ε (τ*σ) u hwr hwi).deriv
    have hsl := (hslope ε (τ*σ) u hε (hε0.trans_le hr02) hδ (hδr.trans_le hr02)
      (by simpa only [abs_of_nonneg hu] using hur₀.trans_le hr02)).2
    rw [abs_of_nonneg hu] at hsl
    constructor
    · rw [hprojection]
      exact (mul_le_mul_of_nonneg_right (min_le_left k₁ (a*ρ^(3/2:ℝ)))
        (Real.rpow_nonneg hL.le _)).trans hcv
    · rw [preferredBump_slope_plateau d B ε τ σ υ u hu huB,← hder]
      exact hsl.trans (div_le_div_of_nonneg_right (le_max_left C₁ (C₂*Real.sqrt R))
        (Real.sqrt_nonneg _))
  · have hρu : ρ ≤ u := le_of_not_gt hur
    obtain ⟨_,hproj,_,hsl⟩ := hcompact ε τ σ υ (-d.b+u)
      (by simpa only [abs_of_pos hε] using hεr.trans_le hη4)
      (by simpa only [abs_of_nonneg hτ] using hτr.trans_le hη4)
      (by constructor <;> linarith) hσ hυ
    have hρL : ρ ≤ L := by dsimp [L]; linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hρ hρL (by norm_num : -(3/2:ℝ) ≤ 0)
    constructor
    · apply le_trans _ hproj
      calc
        k*L^(-(3/2:ℝ)) ≤ (a*ρ^(3/2:ℝ))*L^(-(3/2:ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_right k₁ (a*ρ^(3/2:ℝ))) (Real.rpow_nonneg hL.le _)
        _ ≤ (a*ρ^(3/2:ℝ))*ρ^(-(3/2:ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = a := by rw [mul_assoc,← Real.rpow_add hρ]; norm_num
    · apply hsl.trans
      apply (le_div_iff₀ (Real.sqrt_pos.mpr hL)).mpr
      calc
        C₂*Real.sqrt L ≤ C₂*Real.sqrt R :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLR) hC₂.le
        _ ≤ C := le_max_right _ _


/-- Exact imaginary dispersion formula for the fixed-occupancy bump curve. -/
theorem preferredBumpW_im (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ θ : ℝ) :
    (preferredRadialTrace d ε-Complex.cos (preferredBumpAngle B.m B.p τ σ υ θ)).im =
      (preferredRadialTrace d ε).im-Real.sinh (τ*(σ*B.m θ-υ*B.p θ))*Real.sin θ := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have he : Complex.I*preferredBumpAngle B.m B.p τ σ υ θ =
      ((τ*(σ*B.m θ-υ*B.p θ):ℝ):ℂ)+(θ:ℂ)*Complex.I := by
    unfold preferredBumpAngle
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  calc
    _ = (complexW s (Complex.exp (Complex.I*preferredBumpAngle B.m B.p τ σ υ θ))).im := by
      rw [complexW_exp_I]
      rfl
    _ = _ := by rw [he,complexW_polar_im]; rfl

/-- The exterior radial trace has strictly positive imaginary part. -/
theorem preferredRadialTrace_im_pos (d : PreferredBranchData) {ε : ℝ} (hε : 0 < ε) :
    0 < (preferredRadialTrace d ε).im := by
  have he : 1+ε ≠ 0 := by positivity
  have hs := (IsingBulk.Branch.radial_trace_components d.alpha ε he).2
  change 0 < (IsingBulk.Branch.radialParameter d.alpha ε+
    (IsingBulk.Branch.radialParameter d.alpha ε)⁻¹).im
  rw [hs]
  have hfrac : ε^2/(1+ε) < 2*ε :=
    (div_lt_iff₀ (by positivity : 0 < 1+ε)).mpr (by nlinarith [sq_nonneg ε])
  apply mul_pos (by linarith)
  exact Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt,Real.pi_pos])

/-- Fixed occupancy auxiliaries themselves stay on the physical upper-W
sheet. This is derived from the real sine supports, not imposed on the coarea data. -/
theorem preferredBumpW_im_pos (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ σ υ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hυ : 0 ≤ υ)
    (θ : ℝ) :
    0 < (preferredRadialTrace d ε-Complex.cos (preferredBumpAngle B.m B.p τ σ υ θ)).im := by
  have hsinh : Real.sinh (τ*(σ*B.m θ-υ*B.p θ))*Real.sin θ ≤ 0 := by
    by_cases hs : 0 ≤ Real.sin θ
    · rw [B.m_zero_of_sin_nonneg hs,mul_zero,zero_sub]
      exact mul_nonpos_of_nonpos_of_nonneg
        (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hτ
          (neg_nonpos.mpr (mul_nonneg hυ (B.lower_bound θ))))) hs
    · have hs' : Real.sin θ ≤ 0 := le_of_not_ge hs
      rw [B.p_zero_of_sin_nonpos hs',mul_zero,sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hτ
          (mul_nonneg hσ (B.lower_bound (-θ))))) hs'
  rw [preferredBumpW_im]
  linarith [preferredRadialTrace_im_pos d hε]

/-- Actual fixed-occupancy B=b_s(f) f' on the real u-coordinate. -/
def fixedOccupancySlope (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ u : ℝ) : ℂ :=
  preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u)*
    preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ (-d.b+u)

theorem fixedOccupancySlope_hasDerivAt (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ σ υ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hυ : 0 ≤ υ)
    (u : ℝ) :
    HasDerivAt (fixedOccupancySlope d B ε τ σ υ)
      (-preferredCompactTransportCurvature d B.m B.p (deriv B.m) (deriv B.p)
        (deriv (deriv B.m)) (deriv (deriv B.p)) ε τ σ υ (-d.b+u)) u := by
  have hp' : ContDiff ℝ ∞ (deriv B.p) := (contDiff_infty_iff_deriv.mp B.smooth).2
  have hm' : ContDiff ℝ ∞ (deriv B.m) := (contDiff_infty_iff_deriv.mp B.m_smooth).2
  have h := preferredCompactTransport_hasDerivAt d
    (((contDiff_infty_iff_deriv.mp B.m_smooth).1 (-d.b+u)).hasDerivAt)
    (((contDiff_infty_iff_deriv.mp B.smooth).1 (-d.b+u)).hasDerivAt)
    (((contDiff_infty_iff_deriv.mp hm').1 (-d.b+u)).hasDerivAt)
    (((contDiff_infty_iff_deriv.mp hp').1 (-d.b+u)).hasDerivAt)
    (preferredBumpW_im_pos d B hε hτ hσ hυ (-d.b+u))
  have harg : HasDerivAt (fun v : ℝ => -d.b+v) 1 u := by
    simpa using (hasDerivAt_id u).const_add (-d.b)
  have hd := h.scomp u harg
  simp only [Function.comp_def,one_smul] at hd
  convert! hd using 1

/-- Complete G4 at fixed occupancies on the full right interval, including
all smooth bump transitions. The projected derivative gap follows from the
actual B derivative and the proved plateau/compact curvature estimates. -/
theorem preferred_fixed_occupancy_extreme_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ k ε0 τ0 : ℝ, 0 < k ∧ 0 < ε0 ∧ 0 < τ0 ∧
      ∀ ε τ σ υ m M : ℝ, 0 < ε → ε < ε0 → 0 ≤ τ → τ < τ0 →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → 0 ≤ m → m ≤ M → M ≤ d.b+B.delta →
      k*(2*(M-m)/(Real.sqrt (m+ε+τ*σ)*Real.sqrt (M+ε+τ*σ)*
        (Real.sqrt (m+ε+τ*σ)+Real.sqrt (M+ε+τ*σ)))) ≤
      (preferredCompactDirection*(fixedOccupancySlope d B ε τ σ υ m-
        fixedOccupancySlope d B ε τ σ υ M)).re := by
  obtain ⟨k,_,ε0,τ0,hk,_,hε0,hτ0,hbound⟩ := preferred_full_right_projection d B
  refine ⟨k,ε0,τ0,hk,hε0,hτ0,?_⟩
  intro ε τ σ υ m M hε hεr hτ hτr hσ hυ hm hmM hMR
  let g := fun u : ℝ => (preferredCompactDirection*fixedOccupancySlope d B ε τ σ υ u).re
  let g' := fun u : ℝ => -preferredCompactProjectedCurvature d B.m B.p (deriv B.m) (deriv B.p)
    (deriv (deriv B.m)) (deriv (deriv B.p)) ε τ σ υ (-d.b+u)
  have hg (u : ℝ) (_hu : u ∈ Icc m M) : HasDerivAt g (g' u) u := by
    have hc := (fixedOccupancySlope_hasDerivAt d B hε hτ hσ.1 hυ.1 u).const_mul preferredCompactDirection
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hc
    simpa [g,g',preferredCompactProjectedCurvature,Function.comp_def] using hr
  have hb (u : ℝ) (hu : u ∈ Icc m M) :
      g' u ≤ -k*(u+(ε+τ*σ))^(-(3/2:ℝ)) := by
    have h := (hbound ε τ σ υ u hε hεr hτ hτr hσ hυ
      (hm.trans hu.1) (hu.2.trans hMR)).1
    dsimp [g']
    rw [← add_assoc]
    linarith
  have hE : 0 < m+(ε+τ*σ) := by nlinarith [mul_nonneg hτ hσ.1]
  have hgap := projected_gap_of_deriv_upper (E := ε+τ*σ) hE hmM hg hb
  simpa only [g,← add_assoc,mul_sub,Complex.sub_re] using hgap


/-- The two actual bump-derivative differences have one fixed Lipschitz
constant on the right arc, derived from the C-infinity bump data by compactness. -/
theorem PreferredCoareaBump.derivative_differences {d : PreferredBranchData}
    (B : PreferredCoareaBump d) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, x ∈ Icc (-d.b) B.delta → y ∈ Icc (-d.b) B.delta →
      x ≤ y → |deriv B.p x-deriv B.p y| ≤ K*(y-x) ∧
        |deriv B.m x-deriv B.m y| ≤ K*(y-x) := by
  have hp' : ContDiff ℝ ∞ (deriv B.p) := (contDiff_infty_iff_deriv.mp B.smooth).2
  have hm' : ContDiff ℝ ∞ (deriv B.m) := (contDiff_infty_iff_deriv.mp B.m_smooth).2
  obtain ⟨Cp,hCp⟩ := (isCompact_Icc : IsCompact (Icc (-d.b) B.delta)).exists_bound_of_continuousOn
    (hp'.continuous_deriv (by simp)).continuousOn
  obtain ⟨Cm,hCm⟩ := (isCompact_Icc : IsCompact (Icc (-d.b) B.delta)).exists_bound_of_continuousOn
    (hm'.continuous_deriv (by simp)).continuousOn
  let K := max 0 (max Cp Cm)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hCpK : Cp ≤ K := by dsimp [K]; linarith [le_max_left Cp Cm,le_max_right 0 (max Cp Cm)]
  have hCmK : Cm ≤ K := by dsimp [K]; linarith [le_max_right Cp Cm,le_max_right 0 (max Cp Cm)]
  refine ⟨K,hK,?_⟩
  intro x y hx hy hxy
  have hp := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Icc (-d.b) B.delta) => (contDiff_infty_iff_deriv.mp hp').1 z)
    (fun z hz => (hCp z hz).trans hCpK) (convex_Icc (-d.b) B.delta) hx hy
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Icc (-d.b) B.delta) => (contDiff_infty_iff_deriv.mp hm').1 z)
    (fun z hz => (hCm z hz).trans hCmK) (convex_Icc (-d.b) B.delta) hx hy
  constructor
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy),abs_sub_comm] using hp
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy),abs_sub_comm] using hm

/-- Every actual normalized occupancy lies in the fixed auxiliary box,
with no particle-dependent constants. -/
theorem actual_occupancy_box {N : ℕ} (hN : 0 < N) {d : PreferredBranchData}
    (B : PreferredCoareaBump d) (θ : Fin N → ℝ) :
    occupancy B.p θ/(N:ℝ) ∈ Icc 0 1 ∧ occupancy B.m θ/(N:ℝ) ∈ Icc 0 1 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hsingle (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
      occupancy f θ/(N:ℝ) ∈ Icc 0 1 := by
    have hs0 : 0 ≤ occupancy f θ := Finset.sum_nonneg (fun i _ => hf0 (θ i))
    have hs1 : occupancy f θ ≤ (N:ℝ) := by
      calc
        occupancy f θ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf1 (θ i))
        _ = _ := by simp
    exact ⟨div_nonneg hs0 hNr.le,(div_le_iff₀ hNr).mpr (by simpa using hs1)⟩
  exact ⟨hsingle B.p B.lower_bound B.upper_bound,
    hsingle B.m (fun x => B.lower_bound (-x)) (fun x => B.upper_bound (-x))⟩

/-- The fixed-occupancy comparison curve passes exactly through the actual
balanced contour at its actual occupancy values. -/
theorem actual_bump_angle {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedAngles τ B.p B.m θ i =
      preferredBumpAngle B.m B.p τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i) := by
  unfold deformedAngles balancedShift preferredBumpAngle
  push_cast
  ring

/-- Actual physical phase derivatives at the full configuration have the
same source slopes used in the fixed-occupancy estimates. -/
theorem actual_bump_phase_hasDerivAt {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (preferredAngularPhase d ε)
      (preferredCompactSlope d B.m B.p ε τ (occupancy B.p θ/(N:ℝ))
        (occupancy B.m θ/(N:ℝ)) (θ i)) (deformedAngles τ B.p B.m θ i) := by
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  rw [actual_bump_angle d B τ θ i]
  exact preferredAngularPhase_hasDerivAt d ε (preferredBumpW_im_pos d B hε hτ hσ.1 hυ.1 (θ i))

end
end IsingBulk.Preferred22
