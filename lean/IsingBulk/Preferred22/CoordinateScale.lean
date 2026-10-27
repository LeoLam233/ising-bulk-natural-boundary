import IsingBulk.Preferred22.NegativeCoarea
import IsingBulk.Preferred22.Transport

/-! The actual regular-coordinate endpoints on fixed-occupancy comparison
curves and their all-diameter source scale. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory

def preferredComparisonCoordinate (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ σ υ u : ℝ) : ℂ :=
  let f := preferredBumpAngle B.m B.p τ σ υ (-d.b+u)
  preferredAngularPhase d ε f+f-preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)

theorem preferred_comparison_coordinate_actual {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    preferredComparisonCoordinate d B ε τ (occupancy B.p θ/(N:ℝ))
      (occupancy B.m θ/(N:ℝ)) (θ i+d.b) =
      preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i := by
  unfold preferredComparisonCoordinate
  rw [show -d.b+(θ i+d.b)=θ i by ring,← actual_bump_angle]
  rfl

theorem preferred_bump_first_derivative_bound (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Icc (-Real.pi) Real.pi,
      |deriv B.p θ| ≤ K ∧ |deriv B.m θ| ≤ K := by
  obtain ⟨Cp,hp⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn
    (B.smooth.continuous_deriv (by simp)).continuousOn
  obtain ⟨Cm,hm⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn
    (B.m_smooth.continuous_deriv (by simp)).continuousOn
  refine ⟨1+|Cp|+|Cm|,by positivity,?_⟩
  intro θ hθ
  have hp' := hp θ hθ
  have hm' := hm θ hθ
  rw [Real.norm_eq_abs] at hp' hm'
  constructor <;> linarith [le_abs_self Cp,le_abs_self Cm,abs_nonneg Cp,abs_nonneg Cm]

theorem preferred_bump_tangent_bound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {K τ σ υ θ : ℝ} (_hK : 0 ≤ K) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hσ : σ ∈ Icc 0 1) (hυ : υ ∈ Icc 0 1)
    (hp : |deriv B.p θ| ≤ K) (hm : |deriv B.m θ| ≤ K) :
    ‖preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ θ‖ ≤ 1+2*K := by
  have hdiff : |σ*deriv B.m θ-υ*deriv B.p θ| ≤ 2*K := by
    have htri : |σ*deriv B.m θ-υ*deriv B.p θ| ≤ |σ*deriv B.m θ|+|υ*deriv B.p θ| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (σ*deriv B.m θ) (-(υ*deriv B.p θ))
    rw [abs_mul,abs_mul,abs_of_nonneg hσ.1,abs_of_nonneg hυ.1] at htri
    have hs := mul_le_mul hσ.2 hm (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have hu := mul_le_mul hυ.2 hp (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  calc
    ‖preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ θ‖ ≤
        ‖(1:ℂ)‖+‖Complex.I*(τ:ℂ)*((σ*deriv B.m θ-υ*deriv B.p θ:ℝ):ℂ)‖ := norm_sub_le _ _
    _ = 1+τ*|σ*deriv B.m θ-υ*deriv B.p θ| := by
      rw [norm_one,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
        Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hτ]
    _ ≤ 1+2*K := by
      have h := mul_le_mul hτ1 hdiff (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith

theorem preferred_comparison_angle_hasDerivAt (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ σ υ u : ℝ) :
    HasDerivAt (fun v : ℝ => preferredBumpAngle B.m B.p τ σ υ (-d.b+v))
      (preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ (-d.b+u)) u := by
  have hp := ((contDiff_infty_iff_deriv.mp B.smooth).1 (-d.b+u)).hasDerivAt
  have hm := ((contDiff_infty_iff_deriv.mp B.m_smooth).1 (-d.b+u)).hasDerivAt
  have hi : HasDerivAt (fun v : ℝ => -d.b+v) 1 u := by
    simpa using (hasDerivAt_id u).const_add (-d.b)
  have h := (preferredBumpAngle_hasDerivAt (τ := τ) (σ := σ) (υ := υ) hm hp).scomp u hi
  simp only [Function.comp_def,one_smul] at h
  convert! h using 1

theorem preferred_comparison_coordinate_hasDerivAt (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ σ υ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hσ : 0 ≤ σ) (hυ : 0 ≤ υ) (u : ℝ) :
    HasDerivAt (preferredComparisonCoordinate d B ε τ σ υ)
      ((preferredCompactSlope d B.m B.p ε τ σ υ (-d.b+u)+1)*
        preferredBumpTangent (deriv B.m) (deriv B.p) τ σ υ (-d.b+u)) u := by
  have hi := preferred_comparison_angle_hasDerivAt d B τ σ υ u
  have hp := (preferredAngularPhase_hasDerivAt d ε
    (preferredBumpW_im_pos d B hε hτ hσ hυ (-d.b+u))).scomp u hi
  have h := (hp.add hi).sub_const
    (preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε))
  convert! h using 1
  dsimp [preferredCompactSlope]
  ring

theorem preferred_comparison_coordinate_smooth (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ σ υ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hσ : 0 ≤ σ) (hυ : 0 ≤ υ) :
    ContDiff ℝ ∞ (preferredComparisonCoordinate d B ε τ σ υ) := by
  have hp := B.smooth
  have hm := B.m_smooth
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  let f := fun u : ℝ => preferredBumpAngle B.m B.p τ σ υ (-d.b+u)
  have hf : ContDiff ℝ ∞ f := by dsimp [f,preferredBumpAngle]; fun_prop
  have hφ : ContDiff ℝ ∞ (fun u : ℝ => preferredAngularPhase d ε (f u)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    have hW := preferredBumpW_im_pos d B hε hτ hσ hυ (-d.b+u)
    have ha : AnalyticAt ℂ (preferredAngularPhase d ε) (f u) :=
      AnalyticAt.comp (f := fun w : ℂ => preferredRadialTrace d ε-Complex.cos w)
        (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper hW) (by fun_prop)
    exact ContDiffAt.comp (f := f) (g := preferredAngularPhase d ε) u
      (ha.contDiffAt.restrict_scalars ℝ) hf.contDiffAt
  exact (hφ.add hf).sub contDiff_const

set_option maxHeartbeats 900000 in
/-- Actual regular-coordinate endpoint differences at every diameter scale,
obtained by integrating on the fixed actual-occupancy comparison curve. -/
theorem preferred_fixed_occupancy_coordinate_difference (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ ε τ σ υ u v t r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → -δB ≤ u → u ≤ v → v ≤ d.b+B.delta →
      0 < r → t-2*r ≤ u → v ≤ t+2*r →
      ‖preferredComparisonCoordinate d B ε τ σ υ v-
        preferredComparisonCoordinate d B ε τ σ υ u‖ ≤ C*r/Real.sqrt (|t|+r+ε) := by
  obtain ⟨A,_,ε₀,τ₀,δB,hA,_,hε₀,hτ₀,hδB,hδBδ,_,_,hτ01,hsource⟩ :=
    preferred_full_right_onebody_and_attenuation d B
  obtain ⟨K,hK,hKbound⟩ := preferred_bump_first_derivative_bound d B
  let M := 1+2*K
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨32*A*M,ε₀,τ₀,δB,by positivity,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro ε τ σ υ u v t r hε hεr hτ hτr hσ hυ hu huv hv hr htu hvt
  let Q := preferredComparisonCoordinate d B ε τ σ υ
  have hQ : ContDiff ℝ ∞ Q := preferred_comparison_coordinate_smooth d B hε hτ hσ.1 hυ.1
  have hd (w : ℝ) : HasDerivAt Q (deriv Q w) w := (contDiff_infty_iff_deriv.mp hQ).1 w |>.hasDerivAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w (_ : w ∈ uIcc u v) => hd w)
    ((hQ.continuous_deriv (by simp)).intervalIntegrable u v)
  have hderiv (w : ℝ) (hw : w ∈ Icc u v) : ‖deriv Q w‖ ≤ A*M*preferredOneBodyMajorant ε w := by
    have hwL : -δB ≤ w := hu.trans hw.1
    have hwR : w ≤ d.b+B.delta := hw.2.trans hv
    have hθ : -d.b+w ∈ Icc (-Real.pi) Real.pi := by
      constructor <;> linarith [B.branch_plateau,B.delta_b,d.b_lt,d.b_pos]
    have hb := (hsource ε τ σ υ w hε hεr hτ hτr hσ hυ hwL hwR).1
    have ht := preferred_bump_tangent_bound d B hK.le hτ (hτr.trans_le hτ01).le hσ hυ
      (hKbound (-d.b+w) hθ).1 (hKbound (-d.b+w) hθ).2
    rw [(preferred_comparison_coordinate_hasDerivAt d B hε hτ hσ.1 hυ.1 w).deriv,norm_mul]
    calc
      _ ≤ (A/Real.sqrt (|w|+ε))*M := mul_le_mul hb ht (norm_nonneg _) (by positivity)
      _ = _ := by unfold preferredOneBodyMajorant; ring
  have hmono := intervalIntegral.integral_mono_on (μ := volume) huv
    ((hQ.continuous_deriv (by simp)).norm.intervalIntegrable u v)
    ((continuous_const.mul (preferredOneBodyMajorant_continuous hε)).intervalIntegrable u v) hderiv
  have hscale := intervalIntegral.integral_mono_interval (μ := volume) htu huv hvt
    (Filter.Eventually.of_forall (fun w : ℝ => preferredOneBodyMajorant_nonneg (ε := ε) (u := w)))
    ((preferredOneBodyMajorant_continuous hε).intervalIntegrable (t-2*r) (t+2*r))
  calc
    ‖Q v-Q u‖ = ‖∫ w : ℝ in u..v, deriv Q w‖ := congrArg norm hFTC.symm
    _ ≤ ∫ w : ℝ in u..v, ‖deriv Q w‖ := intervalIntegral.norm_integral_le_integral_norm huv
    _ ≤ ∫ w : ℝ in u..v, A*M*preferredOneBodyMajorant ε w := hmono
    _ = A*M*(∫ w : ℝ in u..v, preferredOneBodyMajorant ε w) := intervalIntegral.integral_const_mul _ _
    _ ≤ A*M*(∫ w : ℝ in (t-2*r)..(t+2*r), preferredOneBodyMajorant ε w) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ A*M*(32*r/Real.sqrt (|t|+r+ε)) :=
      mul_le_mul_of_nonneg_left (preferred_oneBody_mean_scale hε hr t) (by positivity)
    _ = 32*A*M*r/Real.sqrt (|t|+r+ε) := by ring


/-- Source q23 for the literal regular coordinates of any two particles on
one actual coupled contour. The comparison uses the actual occupancies,
held fixed only on the auxiliary one-dimensional integration curve. -/
theorem preferred_actual_coordinate_difference (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ (N : ℕ), 0 < N → ∀ ε τ t r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → ∀ θ : Fin N → ℝ,
      (∀ v, -δB ≤ θ v+d.b ∧ θ v+d.b ≤ d.b+B.delta) →
      (∀ v, t-2*r ≤ θ v+d.b ∧ θ v+d.b ≤ t+2*r) →
      ∀ i j : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i-
        preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ j‖ ≤
        C*r/Real.sqrt (|t|+r+ε) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ :=
    preferred_fixed_occupancy_coordinate_difference d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ t r hε hεr hτ hτr hr θ hbox hwindow i j
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  let σ := occupancy B.p θ/(N:ℝ)
  let υ := occupancy B.m θ/(N:ℝ)
  have heq (v : Fin N) := preferred_comparison_coordinate_actual d B ε τ θ v
  rcases le_total (θ i+d.b) (θ j+d.b) with hij | hji
  · have hh := hbound ε τ σ υ (θ i+d.b) (θ j+d.b) t r hε hεr hτ hτr hσ hυ
      (hbox i).1 hij (hbox j).2 hr (hwindow i).1 (hwindow j).2
    rw [heq j,heq i,norm_sub_rev] at hh
    exact hh
  · have hh := hbound ε τ σ υ (θ j+d.b) (θ i+d.b) t r hε hεr hτ hτr hσ hυ
      (hbox j).1 hji (hbox i).2 hr (hwindow j).1 (hwindow i).2
    rw [heq i,heq j] at hh
    exact hh

/-- The actual regular coordinates remain globally bounded on the physical
right angular strip. This follows directly from the physical inverse-cosine
sheet and needs no prior compact-coordinate-domain hypothesis. -/
theorem preferred_actual_coordinate_global_bound (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ,
      0 < ε → ε ≤ 1 → 0 ≤ τ → τ ≤ 1 → ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc (-Real.pi) Real.pi) → ∀ i : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤ C := by
  let C := 3*Real.pi+15+2*Real.exp 1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N hN ε τ hε hε1 hτ hτ1 θ hθ i
  let w := deformedAngles τ B.p B.m θ i
  have hwi : |w.im| ≤ 1 := (preferred_deformedAngles_im_bound hN d B hτ θ i).trans hτ1
  have hwr : w.re = θ i := by
    simp [w,deformedAngles,Complex.mul_re]
  have hwn : ‖w‖ ≤ Real.pi+1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im w
    have hθa : |θ i| ≤ Real.pi := abs_le.mpr (hθ i)
    rw [hwr] at hh
    linarith
  have hS := preferredRadialTrace_norm_bound d hε.le hε1
  have hWn : ‖preferredRadialTrace d ε-Complex.cos w‖ ≤ 3+Real.exp 1 :=
    (norm_sub_le _ _).trans (add_le_add hS (preferred_cos_norm_le_exp_one hwi))
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hWi : 0 < (preferredRadialTrace d ε-Complex.cos w).im :=
    (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hφ := (preferred_phase_bounds hWi hWn).2.1
  have hBi : 0 < (preferredRadialTrace d ε-1).im := by
    simpa only [Complex.sub_im,Complex.one_im,sub_zero] using preferredRadialTrace_im_pos d hε
  have hBn : ‖preferredRadialTrace d ε-1‖ ≤ 4 := by
    have hh := norm_sub_le (preferredRadialTrace d ε) (1:ℂ)
    rw [norm_one] at hh
    linarith
  have hB := (preferred_phase_bounds hBi hBn).2.1
  have hBn' : ‖preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤ Real.pi+8 := by
    unfold preferredMovingBranch traceMovingBranch
    rw [norm_neg]
    change ‖preferredArccos (preferredRadialTrace d ε-1)‖ ≤ Real.pi+8
    nlinarith only [hB]
  have hh := norm_sub_le
    (preferredSourcePhase τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i+w)
    (preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε))
  have hh2 := norm_add_le
    (preferredSourcePhase τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) w
  change ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤ _ at hh
  change ‖preferredSourcePhase τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤ _ at hφ
  dsimp [C]
  linarith

/-- Positive actual upper occupancy forces a macroscopic mean scale. This
proves the P>0 half of the absolute-coordinate estimate q23 directly on the
actual coupled contour. -/
theorem preferred_actual_coordinate_bound_of_positive_occupancy (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ ε τ t r : ℝ,
      0 < ε → ε ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 < r → ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc (-Real.pi) Real.pi) →
      (∀ i, t-2*r ≤ θ i+d.b ∧ θ i+d.b ≤ t+2*r) →
      0 < occupancy B.p θ → ∀ i : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤ C*Real.sqrt (|t|+r+ε) := by
  obtain ⟨Cg,hCg,hglobal⟩ := preferred_actual_coordinate_global_bound d B
  let C := Cg/Real.sqrt (d.b/2)
  have hbs : 0 < Real.sqrt (d.b/2) := Real.sqrt_pos.mpr (by linarith [d.b_pos])
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N hN ε τ t r hε hε1 hτ hτ1 hr θ hθ hwin hP i
  obtain ⟨a,ha⟩ : ∃ a : Fin N, 0 < B.p (θ a) := by
    by_contra hh
    push Not at hh
    have hz : ∀ a, B.p (θ a)=0 := fun a => le_antisymm (hh a) (B.lower_bound (θ a))
    have hzero : occupancy B.p θ = 0 := by simp only [occupancy,hz,Finset.sum_const_zero]
    linarith
  have hs := B.upper_support (θ a) (hθ a) ha.ne'
  have hT : d.b/2 ≤ |t|+r+ε := by
    linarith [(hwin a).2,hs.1,le_abs_self t,abs_nonneg t]
  have hq := hglobal N hN ε τ hε hε1 hτ hτ1 θ hθ i
  calc
    _ ≤ Cg := hq
    _ = C*Real.sqrt (d.b/2) := by dsimp [C]; field_simp
    _ ≤ C*Real.sqrt (|t|+r+ε) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hT) (by dsimp [C]; positivity)

end
end IsingBulk.Preferred22
