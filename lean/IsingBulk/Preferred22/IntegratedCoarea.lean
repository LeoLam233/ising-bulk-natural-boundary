import IsingBulk.Preferred22.OccupancyCoarea
import IsingBulk.Preferred22.PhaseAttenuation
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Integration of the actual physical extreme pair, with both Jacobian
factors retained until the proved occupancy-dependent coarea estimate. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory

def preferredActualZ {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, physicalRoot (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i))

theorem preferredActualZ_eq_exp {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) :
    preferredActualZ d B ε τ θ = Complex.exp (-Complex.I*preferredTotalPhase d ε τ B.p B.m θ) := by
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hroot (i : Fin N) : physicalRoot (preferredRadialTrace d ε-
      Complex.cos (deformedAngles τ B.p B.m θ i)) =
      Complex.exp (-Complex.I*preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)) :=
    (preferred_phase_physical_root_upper
      ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i))).symm
  unfold preferredActualZ preferredTotalPhase
  simp_rw [hroot]
  rw [← Complex.exp_sum,← Finset.mul_sum]

theorem preferred_actual_oblique_kernel (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ,
      0 < ε → ε < ε₀ → 0 ≤ τ → τ ≤ 1 → ∀ θ : Fin N → ℝ,
      ‖1-preferredActualZ d B ε τ θ‖⁻¹ ≤
        obliqueKernelConstant (Real.cos (3*Real.pi/8)) (Real.sin (3*Real.pi/8)) /
        (c*ε+projectedDistance (Real.cos (3*Real.pi/8))
          (preferredCompactDirection*preferredTotalPhase d ε τ B.p B.m θ).re) := by
  obtain ⟨c,C,hc,_,hphase⟩ := preferred_actual_phase_control d B
  let ε₀ := min 1 (1/c)
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨c,ε₀,hc,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτ1 θ
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hcε1 : c*ε ≤ 1 := by
    have h := (lt_div_iff₀ hc).mp (hεr.trans_le (min_le_right _ _))
    nlinarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : c*ε ≤ -(preferredTotalPhase d ε τ B.p B.m θ).im := by
    have h := (hphase N hN ε τ hε hε1 hτ hτ1 θ).1
    nlinarith [mul_nonneg hc.le hε.le]
  let G := preferredTotalPhase d ε τ B.p B.m θ
  have he : (G.re:ℂ)-Complex.I*((-G.im:ℝ):ℂ)=G := by apply Complex.ext <;> simp
  have h := actual_oblique_periodic_kernel (x := G.re) (a := -G.im)
    (θ := 3*Real.pi/8) (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos])
    (mul_pos hc hε) hcε1 hfloor
  rw [he,← preferredActualZ_eq_exp d B hε hτ θ] at h
  exact h

theorem preferred_phase_denominator_ne_zero {G : ℂ} (hG : G.im < 0) :
    1-Complex.exp (-Complex.I*G) ≠ 0 := by
  intro h
  have he : Complex.exp (-Complex.I*G) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖Complex.exp (-Complex.I*G)‖ < 1 := by
    rw [Complex.norm_exp]
    simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,neg_zero,zero_mul,neg_neg,zero_sub,neg_one_mul] using Real.exp_lt_one_iff.mpr hG
  rw [he,norm_one] at hn
  exact (lt_irrefl (1:ℝ)) hn

theorem extremeAnglePath_add {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (t h : ℝ) :
    extremeAnglePath θ i j (t+h) = extremeAnglePath (extremeAnglePath θ i j t) i j h := by
  ext v
  simp only [extremeAnglePath]
  split_ifs <;> ring

theorem preferred_extreme_deriv_shift {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    deriv (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) t =
      deriv (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m
        (extremeAnglePath (extremeAnglePath θ i j t) i j h)) 0 := by
  simp_rw [← extremeAnglePath_add]
  simpa only [add_zero] using (deriv_comp_const_add
    (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) t 0).symm

theorem preferred_deformed_extreme_smooth {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (θ : Fin N → ℝ) (i j v : Fin N) :
    ContDiff ℝ ∞ (fun h : ℝ => deformedAngles τ B.p B.m (extremeAnglePath θ i j h) v) := by
  have hp := B.smooth
  have hm := B.m_smooth
  have hpath (a : Fin N) : ContDiff ℝ ∞ (fun h : ℝ => extremeAnglePath θ i j h a) := by
    unfold extremeAnglePath
    split_ifs <;> fun_prop
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  unfold deformedAngles balancedShift occupancy
  fun_prop

/-- Actual total phase is genuinely smooth in the real constrained extreme
coordinate on the entire physical contour at positive epsilon. -/
theorem preferred_extreme_phase_smooth {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun h : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) := by
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hterm (v : Fin N) : ContDiff ℝ ∞ (fun h : ℝ =>
      preferredAngularPhase d ε (deformedAngles τ B.p B.m (extremeAnglePath θ i j h) v)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    have him := preferredActualW_im_lower d B hε.le hτ (extremeAnglePath θ i j t) v
    have hW := (mul_pos hε hsin).trans_le him
    have hφ : AnalyticAt ℂ (preferredAngularPhase d ε)
        (deformedAngles τ B.p B.m (extremeAnglePath θ i j t) v) := by
      exact AnalyticAt.comp (f := fun w : ℂ => preferredRadialTrace d ε-Complex.cos w)
        (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper hW) (by fun_prop)
    exact ContDiffAt.comp (f := fun h : ℝ => deformedAngles τ B.p B.m (extremeAnglePath θ i j h) v)
      (g := preferredAngularPhase d ε) t (hφ.contDiffAt.restrict_scalars ℝ)
      (preferred_deformed_extreme_smooth d B τ θ i j v).contDiffAt
  exact ContDiff.sum (fun v (_ : v ∈ Finset.univ) => hterm v)

/-- Continuity of the actual source slopes along the constrained real path. -/
theorem preferred_extreme_slope_continuous {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j v : Fin N) :
    Continuous (fun t : ℝ => actualBumpSlopeVector d B ε τ (extremeAnglePath θ i j t) v) := by
  have he : (fun t : ℝ => actualBumpSlopeVector d B ε τ (extremeAnglePath θ i j t) v) =
      (fun t : ℝ => preferredPhaseSlope (preferredRadialTrace d ε)
        (deformedAngles τ B.p B.m (extremeAnglePath θ i j t) v)) := by
    funext t
    rw [actual_bump_angle]
    rfl
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B (extremeAnglePath θ i j t)
  have hW : 0 < (preferredRadialTrace d ε-
      Complex.cos (deformedAngles τ B.p B.m (extremeAnglePath θ i j t) v)).im := by
    rw [actual_bump_angle]
    exact preferredBumpW_im_pos d B hε hτ hσ.1 hυ.1 _
  exact ContinuousAt.comp (f := fun t : ℝ => deformedAngles τ B.p B.m (extremeAnglePath θ i j t) v)
    (g := preferredPhaseSlope (preferredRadialTrace d ε)) (preferredPhaseSlope_hasDerivAt hW).continuousAt
    (preferred_deformed_extreme_smooth d B τ θ i j v).continuous.continuousAt

def preferredExtremePair {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  ‖(actualBumpSlopeVector d B ε τ θ i+1)*(actualBumpSlopeVector d B ε τ θ j+1)‖

def preferredProjectedPhase {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (preferredCompactDirection*preferredTotalPhase d ε τ B.p B.m θ).re

theorem preferred_extreme_projected_deriv {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    deriv (fun h : ℝ => preferredProjectedPhase d B ε τ (extremeAnglePath θ i j h)) t =
      actualExtremeProjection d B ε τ (extremeAnglePath θ i j t) i j := by
  have hG := (contDiff_infty_iff_deriv.mp (preferred_extreme_phase_smooth d B hε hτ θ i j)).1 t
  have hd := hG.hasDerivAt.const_mul preferredCompactDirection
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have he := hr.deriv
  change deriv (fun h : ℝ => preferredProjectedPhase d B ε τ (extremeAnglePath θ i j h)) t =
    (preferredCompactDirection*deriv (fun h : ℝ =>
      preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j h)) t).re at he
  rw [he,preferred_extreme_deriv_shift]
  rfl

set_option maxHeartbeats 1200000 in
/-- The physical q25 bound on an actual constrained extreme interval. The
hypotheses specify only the geometric support, shell diameter and scale. The
pair/phase derivative bound is derived from the full actual-occupancy G1. -/
theorem preferred_nonnegative_extreme_integral (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N, ∀ x y r T : ℝ,
      x ≤ y → 0 < r → 0 < T →
      (∀ t ∈ Icc x y,
        (∀ v, extremeAnglePath θ i j t v ∈ Icc (-d.b) B.delta) ∧
        (∀ v, extremeAnglePath θ i j t i ≤ extremeAnglePath θ i j t v ∧
          extremeAnglePath θ i j t v ≤ extremeAnglePath θ i j t j) ∧
        r ≤ extremeAnglePath θ i j t j-extremeAnglePath θ i j t i ∧
        extremeAnglePath θ i j t j+d.b+ε ≤ T) →
      (∫ t : ℝ in x..y,
        preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
          ‖1-preferredActualZ d B ε τ (extremeAnglePath θ i j t)‖) ≤
        C*(N:ℝ)*Real.sqrt T/r*(1+|Real.log ε|) := by
  obtain ⟨Cg,εg,τg,hCg,hεg,hτg,hg⟩ := preferred_actual_extreme_estimate d B
  obtain ⟨c,εk,hc,hεk,hkernel⟩ := preferred_actual_oblique_kernel d B
  obtain ⟨cP,Cp,hcP,hCp,hphase⟩ := preferred_actual_phase_control d B
  let ε₀ := min 1 (min εg (min εk (1/c)))
  let τ₀ := min 1 τg
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  let co := Real.cos (3*Real.pi/8)
  let si := Real.sin (3*Real.pi/8)
  have hco : 0 < co := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  let A := obliqueKernelConstant co si
  have hA : 0 < A := by
    apply lt_of_lt_of_le _ (le_max_left _ _)
    dsimp [co]
    positivity
  let P := (co+1/(2*Real.pi))*max 1 co⁻¹*IsingBulk.Tail.simpleKernelConstant
  have hP : 0 < P := by dsimp [P]; positivity [IsingBulk.Tail.simpleKernelConstant_pos]
  let C := A*Cg*P*(1+2*Cp)*(1+|Real.log c|)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,ε₀,τ₀,hC,hε₀,hτ₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ i j x y r T hxy hr hT hgeom
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hεg' : ε < εg := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεk' : ε < εk := hεr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεc' : ε < 1/c := hεr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτ1 : τ ≤ 1 := (hτr.trans_le (min_le_left _ _)).le
  have hτg' : τ < τg := hτr.trans_le (min_le_right _ _)
  have hcε : 0 < c*ε := mul_pos hc hε
  have hcε1 : c*ε ≤ 1 := by nlinarith [(lt_div_iff₀ hc).mp hεc']
  let G := fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)
  let v := fun t : ℝ => preferredProjectedPhase d B ε τ (extremeAnglePath θ i j t)
  let F := fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j
  let Z := fun t : ℝ => preferredActualZ d B ε τ (extremeAnglePath θ i j t)
  let K := Cg*Real.sqrt T/r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : ContDiff ℝ ∞ G := preferred_extreme_phase_smooth d B hε hτ θ i j
  have hv : ContDiff ℝ ∞ v := Complex.reCLM.contDiff.comp (contDiff_const.mul hG)
  have hF : Continuous F :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hvd (t : ℝ) : deriv v t = actualExtremeProjection d B ε τ (extremeAnglePath θ i j t) i j :=
    preferred_extreme_projected_deriv d B hε hτ θ i j t
  have hpair (t : ℝ) (ht : t ∈ uIcc x y) : 0 < deriv v t ∧ F t ≤ K*deriv v t := by
    rw [uIcc_of_le hxy] at ht
    obtain ⟨hbox,hext,hdiam,hscale⟩ := hgeom t ht
    have hsep : extremeAnglePath θ i j t i < extremeAnglePath θ i j t j := by linarith
    have hh := hg N hN ε τ hε hεg' hτ hτg' (extremeAnglePath θ i j t) hbox i j
      (fun a => (hext a).1) (fun a => (hext a).2) hsep
    rw [← hvd t] at hh
    change 0 < deriv v t ∧ F t/deriv v t ≤ _ at hh
    refine ⟨hh.1,(div_le_iff₀ hh.1).mp ?_⟩
    calc
      F t/deriv v t ≤ Cg*Real.sqrt (extremeAnglePath θ i j t j+d.b+ε)/
          (extremeAnglePath θ i j t j-extremeAnglePath θ i j t i) := hh.2
      _ ≤ Cg*Real.sqrt T/(extremeAnglePath θ i j t j-extremeAnglePath θ i j t i) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hscale) hCg.le)
          (sub_nonneg.mpr hsep.le)
      _ ≤ K := div_le_div_of_nonneg_left (by positivity) hr hdiam
  have hcoarea := projected_kernel_coarea_integral (v := v) (v' := deriv v) (F := F) hco hcε hcε1 hxy hK
    (fun t _ => ((contDiff_infty_iff_deriv.mp hv).1 t).hasDerivAt)
    (hv.continuous_deriv (by simp)).continuousOn
    (fun t ht => (hpair t ht).1.le) hF.continuousOn (fun t ht => (hpair t ht).2)
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
    nlinarith only [hh,mul_pos (mul_pos hcP hNp) hε]
  have hleft : Continuous (fun t : ℝ => F t/‖1-Z t‖) :=
    hF.div ((continuous_const.sub hZ).norm) hden
  have hmajor : Continuous (fun t : ℝ => F t/(c*ε+projectedDistance co (v t))) := by
    simpa only [div_eq_mul_inv,Pi.mul_def,Function.comp_def] using
      hF.mul ((projected_reciprocal_continuous hcε).comp hv.continuous)
  have hbound : (∫ t : ℝ in x..y, F t/‖1-Z t‖) ≤
      A*(∫ t : ℝ in x..y, F t/(c*ε+projectedDistance co (v t))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hxy (hleft.intervalIntegrable x y)
      ((continuous_const.mul hmajor).intervalIntegrable x y)
    intro t _
    have hk := hkernel N hN ε τ hε hεk' hτ hτ1 (extremeAnglePath θ i j t)
    change ‖1-Z t‖⁻¹ ≤ A/(c*ε+projectedDistance co (v t)) at hk
    calc
      F t/‖1-Z t‖ = F t*‖1-Z t‖⁻¹ := div_eq_mul_inv _ _
      _ ≤ F t*(A/(c*ε+projectedDistance co (v t))) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = A*(F t/(c*ε+projectedDistance co (v t))) := by ring
  have hvnorm (t : ℝ) : |v t| ≤ Cp*(N:ℝ) := by
    calc
      |v t| ≤ ‖preferredCompactDirection*G t‖ := Complex.abs_re_le_norm _
      _ = ‖G t‖ := by rw [norm_mul,preferredCompactDirection_norm,one_mul]
      _ ≤ Cp*(N:ℝ) := (hphase N hN ε τ hε hε1 hτ hτ1 (extremeAnglePath θ i j t)).2
  have hlen : 1+(v y-v x) ≤ (1+2*Cp)*(N:ℝ) := by
    have hx := abs_le.mp (hvnorm x)
    have hy := abs_le.mp (hvnorm y)
    nlinarith only [hx.1,hy.2,hN1]
  have hlog : 1+|Real.log (c*ε)| ≤ (1+|Real.log c|)*(1+|Real.log ε|) := by
    rw [Real.log_mul hc.ne' hε.ne']
    nlinarith [abs_add_le (Real.log c) (Real.log ε),mul_nonneg (abs_nonneg (Real.log c)) (abs_nonneg (Real.log ε))]
  calc
    (∫ t : ℝ in x..y, F t/‖1-Z t‖) ≤
        A*(∫ t : ℝ in x..y, F t/(c*ε+projectedDistance co (v t))) := hbound
    _ ≤ A*(K*(P*(1+(v y-v x))*(1+|Real.log (c*ε)|))) := mul_le_mul_of_nonneg_left hcoarea hA.le
    _ = (A*K*P)*(1+(v y-v x))*(1+|Real.log (c*ε)|) := by ring
    _ ≤ (A*K*P)*((1+2*Cp)*(N:ℝ))*(1+|Real.log (c*ε)|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen (by positivity)) (by positivity)
    _ ≤ (A*K*P)*((1+2*Cp)*(N:ℝ))*((1+|Real.log c|)*(1+|Real.log ε|)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*(N:ℝ)*Real.sqrt T/r*(1+|Real.log ε|) := by dsimp [C,K]; ring

end
end IsingBulk.Preferred22
