import IsingBulk.HT22.Geometry.SignedCoarea

/-! Genuine signed extreme integration. The all-particle source geometric
estimate is reused with its literal actual occupancy derivatives; the new
phase translation proves uniformity for either affine sign. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory IsingBulk.Preferred22

set_option maxHeartbeats 1200000 in
/-- The physical q25 bound on an actual constrained extreme interval. The
hypotheses specify only the geometric support, shell diameter and scale. The
pair/phase derivative bound is derived from the full actual-occupancy G1. -/
theorem signed_nonnegative_extreme_integral (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
      ∀ a : ℝ, ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
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
          ‖1-signedActualZ a d B ε τ (extremeAnglePath θ i j t)‖) ≤
        C*(N:ℝ)*Real.sqrt T/r*(1+|Real.log ε|) := by
  obtain ⟨Cg,εg,τg,hCg,hεg,hτg,hg⟩ := preferred_actual_extreme_estimate d B
  obtain ⟨c,εk,hc,hεk,hkernel⟩ := signed_actual_oblique_kernel d B
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
  intro a N hN ε τ hε hεr hτ hτr θ i j x y r T hxy hr hT hgeom
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
  let G := fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)+(a:ℂ)
  let v := fun t : ℝ => signedProjectedPhase a d B ε τ (extremeAnglePath θ i j t)
  let F := fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j
  let Z := fun t : ℝ => signedActualZ a d B ε τ (extremeAnglePath θ i j t)
  let K := Cg*Real.sqrt T/r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : ContDiff ℝ ∞ G := (preferred_extreme_phase_smooth d B hε hτ θ i j).add contDiff_const
  have hv : ContDiff ℝ ∞ v := Complex.reCLM.contDiff.comp (contDiff_const.mul hG)
  have hF : Continuous F :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hvd (t : ℝ) : deriv v t = actualExtremeProjection d B ε τ (extremeAnglePath θ i j t) i j :=
    signed_extreme_projected_deriv a d B hε hτ θ i j t
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
      exact signedActualZ_eq_exp a d B hε hτ _
    rw [he]
    fun_prop
  have hden (t : ℝ) : ‖1-Z t‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    change 1-signedActualZ a d B ε τ (extremeAnglePath θ i j t) ≠ 0
    rw [signedActualZ_eq_exp a d B hε hτ]
    apply preferred_phase_denominator_ne_zero
    have hh := (hphase N hN ε τ hε hε1 hτ hτ1 (extremeAnglePath θ i j t)).1
    have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
    simp only [Complex.add_im,Complex.ofReal_im,add_zero]
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
    have hk := hkernel a N hN ε τ hε hεk' hτ hτ1 (extremeAnglePath θ i j t)
    change ‖1-Z t‖⁻¹ ≤ A/(c*ε+projectedDistance co (v t)) at hk
    calc
      F t/‖1-Z t‖ = F t*‖1-Z t‖⁻¹ := div_eq_mul_inv _ _
      _ ≤ F t*(A/(c*ε+projectedDistance co (v t))) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = A*(F t/(c*ε+projectedDistance co (v t))) := by ring
  have hvnorm (t : ℝ) : |preferredProjectedPhase d B ε τ (extremeAnglePath θ i j t)| ≤ Cp*(N:ℝ) := by
    calc
      _ ≤ ‖preferredCompactDirection*preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)‖ := Complex.abs_re_le_norm _
      _ = ‖preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)‖ := by
        rw [norm_mul,preferredCompactDirection_norm,one_mul]
      _ ≤ Cp*(N:ℝ) := (hphase N hN ε τ hε hε1 hτ hτ1 (extremeAnglePath θ i j t)).2
  have hlen : 1+(v y-v x) ≤ (1+2*Cp)*(N:ℝ) := by
    have hx := abs_le.mp (hvnorm x)
    have hy := abs_le.mp (hvnorm y)
    have hvsub : v y-v x = preferredProjectedPhase d B ε τ (extremeAnglePath θ i j y)-
        preferredProjectedPhase d B ε τ (extremeAnglePath θ i j x) := by
      dsimp [v]
      rw [signedProjectedPhase_shift,signedProjectedPhase_shift]
      ring
    rw [hvsub]
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
end IsingBulk.HT22.Geometry
