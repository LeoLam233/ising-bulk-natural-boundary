import IsingBulk.Analysis.BranchModulus
import IsingBulk.Analysis.BranchDerivative

/-! Uniform two-sided size of the derivative of the actual current. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem currentDu_zero (d : LocalBranchData) : currentDu d 0 0 0 = (d.a:ℂ) := by
  simp [currentDu,LocalBranchData.a,Complex.sinh_mul_I,← Complex.ofReal_sin,mul_assoc]

theorem currentDu_continuous (d : LocalBranchData) :
    Continuous (fun z : ℝ × ℝ × ℝ => currentDu d z.1 z.2.1 z.2.2) := by
  unfold currentDu
  fun_prop

theorem current_factors_near_zero (d : LocalBranchData) :
    ∀ᶠ z in 𝓝 (0:ℝ × ℝ × ℝ),
      d.a/2 ≤ ‖currentDu d z.1 z.2.1 z.2.2‖ ∧
      ‖currentDu d z.1 z.2.1 z.2.2‖ ≤ 2*d.a ∧
      1 ≤ ‖2-currentD d z.1 z.2.1 z.2.2‖ ∧
      ‖2-currentD d z.1 z.2.1 z.2.2‖ ≤ 3 := by
  have hdu := (currentDu_continuous d).norm.continuousAt (x := (0:ℝ × ℝ × ℝ))
  have hd : ContinuousAt (fun z : ℝ × ℝ × ℝ => ‖2-currentD d z.1 z.2.1 z.2.2‖) 0 :=
    ((currentW_continuous d).const_sub 1 |>.const_sub 2).norm
  have hdu0 : ‖currentDu d 0 0 0‖ = d.a := by
    rw [currentDu_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos d.a_pos]
  have hd0 : ‖2-currentD d 0 0 0‖ = 2 := by simp [currentD,currentW_zero]
  have ha := d.a_pos
  filter_upwards [(continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => d.a/2) 0).eventually_lt hdu
      (by change d.a/2 < ‖currentDu d 0 0 0‖; rw [hdu0]; linarith),
    hdu.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => 2*d.a) 0)
      (by change ‖currentDu d 0 0 0‖ < 2*d.a; rw [hdu0]; linarith),
    (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => (1:ℝ)) 0).eventually_lt hd
      (by change 1 < ‖2-currentD d 0 0 0‖; rw [hd0]; norm_num),
    hd.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => (3:ℝ)) 0)
      (by change ‖2-currentD d 0 0 0‖ < 3; rw [hd0]; norm_num)]
      with z h₁ h₂ h₃ h₄
  exact ⟨h₁.le,h₂.le,h₃.le,h₄.le⟩

theorem sqrt_quotient_bounds (v h L a c C : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C) (hL : 0 < L)
    (hv : a/2 ≤ v) (hv' : v ≤ 2*a) (hh : c*L ≤ h) (hh' : h ≤ C*L) :
    (a/(2*Real.sqrt C))/Real.sqrt L ≤ v/Real.sqrt h ∧
      v/Real.sqrt h ≤ (2*a/Real.sqrt c)/Real.sqrt L := by
  have hhpos : 0 < h := (mul_pos hc hL).trans_le hh
  have hs := Real.sqrt_pos.mpr hhpos
  have hsL := Real.sqrt_pos.mpr hL
  have hsc := Real.sqrt_pos.mpr hc
  have hsC := Real.sqrt_pos.mpr hC
  have hb := Real.sqrt_le_sqrt hh
  have hb' := Real.sqrt_le_sqrt hh'
  rw [Real.sqrt_mul hc.le] at hb
  rw [Real.sqrt_mul hC.le] at hb'
  constructor
  · have he : (a/(2*Real.sqrt C))/Real.sqrt L = (a/2)/(Real.sqrt C*Real.sqrt L) := by ring
    rw [he]
    exact div_le_div₀ (by linarith) hv hs hb'
  · have he : (2*a/Real.sqrt c)/Real.sqrt L = (2*a)/(Real.sqrt c*Real.sqrt L) := by ring
    rw [he]
    exact div_le_div₀ (by positivity) hv' (mul_pos hsc hsL) hb

theorem current_derivative_magnitude_Q (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      c/Real.sqrt (|u|+ε+d.tau*t) ≤ ‖deriv (currentPhase d ε t) u‖ ∧
      ‖deriv (currentPhase d ε t) u‖ ≤ C/Real.sqrt (|u|+ε+d.tau*t) := by
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmod⟩ := current_modulus_Q d
  obtain ⟨r₂,hr₂,hbranch⟩ := current_branch_inclusion d
  obtain ⟨r₃,hr₃,hfactors⟩ := Metric.eventually_nhds_iff.mp (current_factors_near_zero d)
  let r := min r₁ (min r₂ r₃)
  have ha := d.a_pos
  refine ⟨d.a/(2*Real.sqrt (3*C)),2*d.a/Real.sqrt c,r,by positivity,by positivity,
    lt_min hr₁ (lt_min hr₂ hr₃),?_⟩
  intro ε t u hε hεr ht htr hur
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₃ : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hm,hm'⟩ := hmod ε t u hε (hεr.trans_le hrr₁) ht (htr.trans_le hrr₁) (hur.trans_le hrr₁)
  obtain ⟨hre,him⟩ := hbranch ε t u hε (hεr.trans_le hrr₂) ht (htr.trans_le hrr₂) (hur.trans_le hrr₂)
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₃ := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht]
      using And.intro (hεr.trans_le hrr₃) (And.intro (htr.trans_le hrr₃) (hur.trans_le hrr₃))
  obtain ⟨hv,hv',hf,hf'⟩ := hfactors hz
  have hL : 0 < |u|+ε+d.tau*t := by nlinarith [abs_nonneg u,mul_nonneg d.tau_pos.le ht]
  rw [currentPhase_deriv_norm d ε t u hre him,norm_mul]
  apply sqrt_quotient_bounds _ _ _ _ _ _ ha hc (by positivity) hL hv hv'
  · nlinarith [mul_le_mul_of_nonneg_left hf (norm_nonneg (currentD d ε t u))]
  · nlinarith [mul_le_mul hm' hf' (norm_nonneg _) (by positivity : 0 ≤ C*(|u|+ε+d.tau*t))]

theorem current_derivative_magnitude (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      c/Real.sqrt (|u|+ε+t) ≤ ‖deriv (currentPhase d ε t) u‖ ∧
      ‖deriv (currentPhase d ε t) u‖ ≤ C/Real.sqrt (|u|+ε+t) := by
  obtain ⟨c,C,r,hc,hC,hr,h⟩ := current_derivative_magnitude_Q d
  have hmin : 0 < min 1 d.tau := lt_min zero_lt_one d.tau_pos
  have hmax : 0 < max 1 d.tau := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c/Real.sqrt (max 1 d.tau),C/Real.sqrt (min 1 d.tau),r,by positivity,by positivity,hr,?_⟩
  intro ε t u hε hεr ht htr hur
  obtain ⟨hl,hu⟩ := h ε t u hε hεr ht htr hur
  let L := |u|+ε+t
  let Q := |u|+ε+d.tau*t
  have hL : 0 < L := by dsimp [L]; positivity
  have hQ : 0 < Q := by dsimp [Q]; nlinarith [abs_nonneg u,mul_nonneg d.tau_pos.le ht]
  have hlo : min 1 d.tau*L ≤ Q := by
    dsimp [L,Q]
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 d.tau) (abs_nonneg u),
      mul_le_mul_of_nonneg_right (min_le_left 1 d.tau) hε.le,
      mul_le_mul_of_nonneg_right (min_le_right 1 d.tau) ht]
  have hhi : Q ≤ max 1 d.tau*L := by
    dsimp [L,Q]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 d.tau) (abs_nonneg u),
      mul_le_mul_of_nonneg_right (le_max_left 1 d.tau) hε.le,
      mul_le_mul_of_nonneg_right (le_max_right 1 d.tau) ht]
  have hslo := Real.sqrt_le_sqrt hlo
  have hshi := Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul hmin.le] at hslo
  rw [Real.sqrt_mul hmax.le] at hshi
  constructor
  · apply le_trans _ hl
    change (c/Real.sqrt (max 1 d.tau))/Real.sqrt L ≤ c/Real.sqrt Q
    rw [div_div]
    exact div_le_div₀ hc.le le_rfl (Real.sqrt_pos.mpr hQ) hshi
  · apply le_trans hu
    change C/Real.sqrt Q ≤ (C/Real.sqrt (min 1 d.tau))/Real.sqrt L
    rw [div_div]
    exact div_le_div₀ hC.le le_rfl (mul_pos (Real.sqrt_pos.mpr hmin) (Real.sqrt_pos.mpr hL)) hslo

theorem original_derivative_magnitude (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → |u| < r →
      c/Real.sqrt (|u|+ε) ≤ ‖deriv (originalPhase d ε) u‖ ∧
      ‖deriv (originalPhase d ε) u‖ ≤ C/Real.sqrt (|u|+ε) := by
  obtain ⟨c,C,r,hc,hC,hr,h⟩ := current_derivative_magnitude d
  refine ⟨c,C,r,hc,hC,hr,?_⟩
  intro ε u hε hεr hur
  have he : originalPhase d ε = currentPhase d ε 0 := by funext x; rfl
  rw [he]
  simpa only [add_zero] using h ε 0 u hε hεr le_rfl hr hur

end
end IsingBulk.Branch
