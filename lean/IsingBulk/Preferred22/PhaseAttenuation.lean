import IsingBulk.Preferred22.BumpCoarea

/-! Literal physical-phase bounds on the entire balanced angular contour.
The constants below are independent of the number of particles and angles. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set

/-- The same explicit phase identifies the globally chosen physical root
throughout the whole upper W-half-plane, including its left half. -/
theorem preferred_phase_physical_root_upper {W : ℂ} (hW : 0 < W.im) :
    Complex.exp (-Complex.I*preferredArccos W) = physicalRoot W := by
  rw [preferred_exp_phase_inverse]
  apply root_unique_in_disk (W := W)
  · simpa only [inv_inv,add_comm] using preferredCosineRoot_trace W
  · exact physicalRoot_trace W
  · exact inv_ne_zero (preferredCosineRoot_ne_zero W)
  · exact physicalRoot_ne_zero W
  · rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ (IsingBulk.Branch.inverseCosineRoot_norm_of_upper hW)
  · exact physicalRoot_inside (Or.inl hW.ne')

/-- A trace bound controls the inverse-cosine root without a logarithm or
square-root branch estimate at the endpoints. -/
theorem preferredCosineRoot_norm_bound {W : ℂ} {R : ℝ}
    (hW : 0 < W.im) (hR : ‖W‖ ≤ R) : ‖preferredCosineRoot W‖ ≤ 2*R+1 := by
  let z := preferredCosineRoot W
  have hz : 1 < ‖z‖ := IsingBulk.Branch.inverseCosineRoot_norm_of_upper hW
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv,← one_div]
    exact (div_le_one₀ (by positivity : 0 < ‖z‖)).mpr hz.le
  rw [norm_inv] at hinv
  have he : z = 2*W-z⁻¹ := by
    have ht := preferredCosineRoot_trace W
    change z+z⁻¹=2*W at ht
    linear_combination ht
  calc
    ‖preferredCosineRoot W‖ = ‖2*W-z⁻¹‖ := congrArg norm he
    _ ≤ ‖2*W‖+‖z⁻¹‖ := norm_sub_le _ _
    _ ≤ 2*R+1 := by rw [norm_mul]; norm_num; nlinarith

/-- Exact attenuation is the positive logarithm of the reciprocal physical
root. The full upper sheet also bounds the real phase by pi. -/
theorem preferred_phase_bounds {W : ℂ} {R : ℝ}
    (hW : 0 < W.im) (hR : ‖W‖ ≤ R) :
    0 < -(preferredArccos W).im ∧
    ‖preferredArccos W‖ ≤ Real.pi+2*R ∧
    W.im ≤ (2*R+1)*(-(preferredArccos W).im) := by
  let z := preferredCosineRoot W
  let r := ‖z‖
  have hr1 : 1 < r := IsingBulk.Branch.inverseCosineRoot_norm_of_upper hW
  have hr : 0 < r := by linarith
  have hzi : 0 < z.im := IsingBulk.Branch.inverseCosineRoot_im_pos_of_upper hW
  have hrR : r ≤ 2*R+1 := preferredCosineRoot_norm_bound hW hR
  have hlog : -(preferredArccos W).im = Real.log r := by
    dsimp [preferredArccos,r,z,preferredCosineRoot]
    simp [Complex.mul_im,Complex.log_re]
  have hsheet := IsingBulk.Branch.lowerArccos_sheet_of_upper hW
  change Complex.cos (preferredArccos W) = W ∧ 0 < (preferredArccos W).re ∧
    (preferredArccos W).re < Real.pi ∧ (preferredArccos W).im < 0 at hsheet
  have hnorm : ‖preferredArccos W‖ ≤ Real.pi+2*R := by
    have h := Complex.norm_le_abs_re_add_abs_im (preferredArccos W)
    rw [abs_of_pos hsheet.2.1,abs_of_neg hsheet.2.2.2,hlog] at h
    linarith [Real.log_le_sub_one_of_pos hr]
  have ht := congrArg Complex.im (preferredCosineRoot_trace W)
  change (z+z⁻¹).im = (2*W).im at ht
  simp only [Complex.add_im,Complex.inv_im,Complex.normSq_eq_norm_sq,
    Complex.mul_im] at ht
  norm_num at ht
  have he : 2*W.im = z.im*(1-1/r^2) := by dsimp [r]; linear_combination -ht
  have hfac : 0 ≤ 1-1/r^2 := by
    have hh : 1/r^2 ≤ 1 := (div_le_one₀ (sq_pos_of_pos hr)).mpr (by nlinarith)
    linarith
  have hzim : z.im ≤ r := Complex.im_le_norm z
  have him : 2*W.im ≤ r*(1-1/r^2) := by rw [he]; exact mul_le_mul_of_nonneg_right hzim hfac
  have harith : r*(1-1/r^2) ≤ 2*(r-1) := by
    field_simp
    nlinarith [sq_nonneg (r-1)]
  have hloglower := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr) hr.le
  have hloglower' : r-1 ≤ r*Real.log r := by
    simpa only [mul_sub,mul_one,mul_inv_cancel₀ hr.ne'] using hloglower
  have hlogpos : 0 < Real.log r := Real.log_pos hr1
  refine ⟨by rw [hlog]; exact hlogpos,hnorm,?_⟩
  rw [hlog]
  calc
    W.im ≤ r-1 := by linarith
    _ ≤ r*Real.log r := hloglower'
    _ ≤ (2*R+1)*Real.log r := mul_le_mul_of_nonneg_right hrR hlogpos.le

/-- Uniform bounded-strip estimate for the actual complex cosine. -/
theorem preferred_cos_norm_le_exp_one {w : ℂ} (hw : |w.im| ≤ 1) :
    ‖Complex.cos w‖ ≤ Real.exp 1 := by
  have hc := Real.cosh_le_cosh.mpr (show |w.im| ≤ |(1:ℝ)| by simpa using hw)
  have hs := Real.sinh_le_sinh.mpr hw
  have habs : |Real.sinh w.im| ≤ Real.sinh 1 := by rwa [Real.abs_sinh]
  have hcos := Real.abs_cos_le_one w.re
  have hsin := Real.abs_sin_le_one w.re
  calc
    ‖Complex.cos w‖ ≤ |(Complex.cos w).re|+|(Complex.cos w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.cos w.re| * Real.cosh w.im+|Real.sin w.re| * |Real.sinh w.im| := by
      simp only [Complex.cos_eq w]
      simp [Complex.mul_re,Complex.mul_im,abs_mul,abs_of_pos (Real.cosh_pos _)]
      rfl
    _ ≤ Real.cosh 1+Real.sinh 1 := by
      have h₁ := mul_le_mul hcos hc (Real.cosh_pos w.im).le (by norm_num : (0:ℝ) ≤ 1)
      have h₂ := mul_le_mul hsin habs (abs_nonneg (Real.sinh w.im)) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith
    _ = Real.exp 1 := Real.cosh_add_sinh _

theorem preferredRadialTrace_norm_bound (d : PreferredBranchData) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : ‖preferredRadialTrace d ε‖ ≤ 3 := by
  have hn : ‖IsingBulk.Branch.radialParameter d.alpha ε‖ = 1+ε := by
    simp only [IsingBulk.Branch.radialParameter,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I,abs_of_nonneg (by positivity : 0 ≤ 1+ε),mul_one]
  calc
    ‖preferredRadialTrace d ε‖ ≤ ‖IsingBulk.Branch.radialParameter d.alpha ε‖+
        ‖(IsingBulk.Branch.radialParameter d.alpha ε)⁻¹‖ := norm_add_le _ _
    _ = 1+ε+(1+ε)⁻¹ := by rw [norm_inv,hn]
    _ ≤ 3 := by
      have hi : (1+ε)⁻¹ ≤ 1 := by
        rw [← one_div]
        exact (div_le_one₀ (by positivity : 0 < 1+ε)).mpr (by linarith)
      linarith

theorem preferredRadialTrace_im_lower (d : PreferredBranchData) {ε : ℝ}
    (hε : 0 ≤ ε) : ε*Real.sin d.alpha ≤ (preferredRadialTrace d ε).im := by
  have he : 1+ε ≠ 0 := by positivity
  have hs := (IsingBulk.Branch.radial_trace_components d.alpha ε he).2
  change _ ≤ (IsingBulk.Branch.radialParameter d.alpha ε+
    (IsingBulk.Branch.radialParameter d.alpha ε)⁻¹).im
  rw [hs]
  have hfrac : ε^2/(1+ε) ≤ ε :=
    (div_le_iff₀ (by positivity : 0 < 1+ε)).mpr (by nlinarith)
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt,Real.pi_pos])).le

/-- The imaginary dispersion margin on the complete actual balanced contour,
with the occupancies computed at that same angular configuration. -/
theorem preferredActualW_im_lower {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (θ : Fin N → ℝ) (i : Fin N) :
    ε*Real.sin d.alpha ≤ (preferredRadialTrace d ε-
      Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
  have h := homotopy_complexW_im_ge (s := IsingBulk.Branch.radialParameter d.alpha ε)
    hτ (by norm_num : (0:ℝ) ≤ 1) B.p B.m θ B.lower_bound
    (fun x => B.lower_bound (-x)) (fun x hx => B.p_zero_of_sin_nonpos hx)
    (fun x hx => B.m_zero_of_sin_nonneg hx) i
  rw [complexW_homotopyRoot_eq] at h
  exact (preferredRadialTrace_im_lower d hε).trans h

/-- Actual coupled contour heights are bounded by tau, uniformly in N. -/
theorem preferred_deformedAngles_im_bound {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ}
    (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i : Fin N) :
    |(deformedAngles τ B.p B.m θ i).im| ≤ τ := by
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  rw [actual_bump_angle d B τ θ i]
  simp only [preferredBumpAngle,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,mul_zero,one_mul,zero_add,zero_sub,abs_neg]
  have hm0 := B.lower_bound (-θ i)
  have hm1 := B.upper_bound (-θ i)
  have hp0 := B.lower_bound (θ i)
  have hp1 := B.upper_bound (θ i)
  have hm : 0 ≤ occupancy B.p θ/(N:ℝ)*B.m (θ i) ∧
      occupancy B.p θ/(N:ℝ)*B.m (θ i) ≤ 1 := by
    constructor
    · exact mul_nonneg hσ.1 hm0
    · exact (mul_le_mul hσ.2 hm1 hm0 (by norm_num)).trans_eq (one_mul 1)
  have hp : 0 ≤ occupancy B.m θ/(N:ℝ)*B.p (θ i) ∧
      occupancy B.m θ/(N:ℝ)*B.p (θ i) ≤ 1 := by
    constructor
    · exact mul_nonneg hυ.1 hp0
    · exact (mul_le_mul hυ.2 hp1 hp0 (by norm_num)).trans_eq (one_mul 1)
  rw [abs_mul,abs_of_nonneg hτ]
  have ha : |occupancy B.p θ/(N:ℝ)*B.m (θ i)-occupancy B.m θ/(N:ℝ)*B.p (θ i)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hm.1,hm.2,hp.1,hp.2]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ha hτ

/-- Uniform attenuation floor and bounded phase on the original actual
complete contour; no cutoff restriction or particle-order bound is used. -/
theorem preferred_actual_phase_control (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 0 < N →
      ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ τ → τ ≤ 1 → ∀ θ : Fin N → ℝ,
      c*(N:ℝ)*ε ≤ -(preferredTotalPhase d ε τ B.p B.m θ).im ∧
      ‖preferredTotalPhase d ε τ B.p B.m θ‖ ≤ C*(N:ℝ) := by
  let R := 3+Real.exp 1
  let c := Real.sin d.alpha/(2*R+1)
  let C := Real.pi+2*R
  have hR : 0 < R := by dsimp [R]; positivity
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c,C,hc,hC,?_⟩
  intro N hN ε τ hε hε1 hτ hτ1 θ
  have hpoint (i : Fin N) :
      c*ε ≤ -(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im ∧
      ‖preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)‖ ≤ C := by
    let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
    have him := preferredActualW_im_lower d B hε.le hτ θ i
    have hWp : 0 < W.im := (mul_pos hε hsin).trans_le him
    have hWn : ‖W‖ ≤ R := by
      have hw := (preferred_deformedAngles_im_bound hN d B hτ θ i).trans hτ1
      exact (norm_sub_le _ _).trans (add_le_add (preferredRadialTrace_norm_bound d hε.le hε1)
        (preferred_cos_norm_le_exp_one hw))
    obtain ⟨_,hn,ha⟩ := preferred_phase_bounds hWp hWn
    change c*ε ≤ -(preferredArccos W).im ∧ ‖preferredArccos W‖ ≤ C
    refine ⟨?_,hn⟩
    dsimp [c]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : 0 < 2*R+1)).mpr (by nlinarith)
  constructor
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hpoint i).1)
    have he : (preferredTotalPhase d ε τ B.p B.m θ).im =
        ∑ i, (preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im :=
      map_sum Complex.imCLM _ _
    rw [he]
    simp only [Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul] at h
    nlinarith only [h]
  · calc
      ‖preferredTotalPhase d ε τ B.p B.m θ‖ ≤
        ∑ i, ‖preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => (hpoint i).2)
      _ = C*(N:ℝ) := by simp [mul_comm]

end
end IsingBulk.Preferred22
