import IsingBulk.Analysis.BranchTaylor

/-! Actual imaginary margin at the radial center, with the current height
held fixed during the angular variation. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

def sinhQuotient (v : ℝ) : ℝ := dslope Real.sinh 0 v

theorem sinhQuotient_zero : sinhQuotient 0 = 1 := by
  simp [sinhQuotient,Real.deriv_sinh]

theorem sinhQuotient_continuous : ContinuousAt sinhQuotient 0 :=
  continuousAt_dslope_same.mpr (Real.hasDerivAt_sinh 0).differentiableAt

theorem sinhQuotient_identity (v : ℝ) : v*sinhQuotient v = Real.sinh v := by
  simpa [sinhQuotient,smul_eq_mul] using sub_smul_dslope Real.sinh 0 v

def betaE (d : LocalBranchData) (z : ℝ × ℝ × ℝ) : ℝ :=
  (2-z.1/(1+z.1))*Real.sin d.theta+
    d.c₀*sinhQuotient (-d.c₀*z.1+d.tau*z.2.1/2)*Real.sin (-d.thetaB+z.2.2)

def betaT (d : LocalBranchData) (z : ℝ × ℝ × ℝ) : ℝ :=
  -sinhQuotient (-d.c₀*z.1+d.tau*z.2.1/2)*Real.sin (-d.thetaB+z.2.2)/2

theorem beta_coefficients_continuous (d : LocalBranchData) :
    ContinuousAt (betaE d) 0 ∧ ContinuousAt (betaT d) 0 := by
  have hh : ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      sinhQuotient (-d.c₀*z.1+d.tau*z.2.1/2)) 0 :=
    ContinuousAt.comp (g := sinhQuotient) (f := fun z : ℝ × ℝ × ℝ =>
      -d.c₀*z.1+d.tau*z.2.1/2) (by simpa using sinhQuotient_continuous) (by fun_prop)
  constructor
  · unfold betaE; fun_prop (disch := norm_num)
  · unfold betaT; fun_prop

theorem beta_coefficients_zero (d : LocalBranchData) :
    betaE d 0 = d.b ∧ betaT d 0 = d.a/2 := by
  simp [betaE,betaT,sinhQuotient_zero,LocalBranchData.a,LocalBranchData.b]
  ring

theorem current_imaginary_factorization (d : LocalBranchData) (ε t u : ℝ)
    (hε : 1+ε ≠ 0) :
    (currentW d ε t u).im = ε*betaE d (ε,t,u)+d.tau*t*betaT d (ε,t,u) := by
  have hi := (current_components d ε t u hε).2
  have hsq := sinhQuotient_identity (-d.c₀*ε+d.tau*t/2)
  simp only [currentD,Complex.sub_im,Complex.one_im,zero_sub,neg_neg] at hi
  rw [hi,← hsq]
  unfold betaE betaT
  ring

theorem beta_coefficients_near_zero (d : LocalBranchData) :
    ∀ᶠ z in 𝓝 (0:ℝ × ℝ × ℝ),
      d.b/2 ≤ betaE d z ∧ betaE d z ≤ 2*d.b ∧
      d.a/4 ≤ betaT d z ∧ betaT d z ≤ d.a := by
  obtain ⟨he,ht⟩ := beta_coefficients_continuous d
  obtain ⟨he0,ht0⟩ := beta_coefficients_zero d
  have ha := d.a_pos
  have hb := d.b_pos
  filter_upwards [continuousAt_const.eventually_lt he (by rw [he0]; linarith : d.b/2 < betaE d 0),
    he.eventually_lt continuousAt_const (by rw [he0]; linarith : betaE d 0 < 2*d.b),
    continuousAt_const.eventually_lt ht (by rw [ht0]; linarith : d.a/4 < betaT d 0),
    ht.eventually_lt continuousAt_const (by rw [ht0]; linarith : betaT d 0 < d.a)] with z h₁ h₂ h₃ h₄
  exact ⟨h₁.le,h₂.le,h₃.le,h₄.le⟩

theorem current_imaginary_margin (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      c*(ε+d.tau*t) ≤ (currentW d ε t u).im ∧
        (currentW d ε t u).im ≤ C*(ε+d.tau*t) := by
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (beta_coefficients_near_zero d)
  have ha := d.a_pos
  have hb := d.b_pos
  refine ⟨min (d.b/2) (d.a/4),max (2*d.b) d.a,r,by positivity,by positivity,hr,?_⟩
  intro ε t u hε hεr ht htr hur
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht]
      using And.intro hεr (And.intro htr hur)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hball hz
  rw [current_imaginary_factorization d ε t u (by linarith)]
  have he := min_le_left (d.b/2) (d.a/4)
  have ht' := min_le_right (d.b/2) (d.a/4)
  have he' := le_max_left (2*d.b) d.a
  have ht'' := le_max_right (2*d.b) d.a
  have hτt : 0 ≤ d.tau*t := mul_nonneg d.tau_pos.le ht
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (he.trans h₁) hε.le,
      mul_le_mul_of_nonneg_left (ht'.trans h₃) hτt]
  · nlinarith [mul_le_mul_of_nonneg_left (h₂.trans he') hε.le,
      mul_le_mul_of_nonneg_left (h₄.trans ht'') hτt]

theorem currentW_zero (d : LocalBranchData) : currentW d 0 0 0 = 1 := by
  have h := branchDModel_eq d 0 0 0 (by norm_num)
  simp only [Complex.ofReal_zero] at h
  change branchDModel d 0 = 1-currentW d 0 0 0 at h
  rw [branchDModel_zero] at h
  linear_combination h

theorem currentW_continuous (d : LocalBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ => currentW d z.1 z.2.1 z.2.2) 0 := by
  unfold currentW plateauW radialParameter
  fun_prop (disch := simp [Complex.exp_ne_zero])

set_option maxHeartbeats 800000 in
/-- The actual radial current lies on the previously proved fourth-quadrant
inverse-cosine sheet. The radius is fixed before the three varying coordinates. -/
theorem current_branch_inclusion (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      0 < (currentW d ε t u).re ∧ 0 < (currentW d ε t u).im := by
  obtain ⟨c,C,r,hc,_,hr,hmargin⟩ := current_imaginary_margin d
  have hre : ContinuousAt (fun z : ℝ × ℝ × ℝ => (currentW d z.1 z.2.1 z.2.2).re) 0 :=
    Complex.continuous_re.continuousAt.comp (currentW_continuous d)
  have hp := continuousAt_const.eventually_lt hre
    (show (0:ℝ) < (currentW d 0 0 0).re by rw [currentW_zero]; norm_num)
  obtain ⟨r',hr',hball⟩ := Metric.eventually_nhds_iff.mp hp
  refine ⟨min r r',lt_min hr hr',?_⟩
  intro ε t u hε hεr ht htr hur
  have hm := (hmargin ε t u hε (hεr.trans_le (min_le_left _ _)) ht
    (htr.trans_le (min_le_left _ _)) (hur.trans_le (min_le_left _ _))).1
  have hscale : 0 < ε+d.tau*t := add_pos_of_pos_of_nonneg hε (mul_nonneg d.tau_pos.le ht)
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r' := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht]
      using And.intro (hεr.trans_le (min_le_right _ _))
        (And.intro (htr.trans_le (min_le_right _ _)) (hur.trans_le (min_le_right _ _)))
  exact ⟨hball hz,lt_of_lt_of_le (mul_pos hc hscale) hm⟩

theorem current_phase_sheet (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      Complex.cos (currentPhase d ε t u) = currentW d ε t u ∧
      0 < (currentPhase d ε t u).re ∧ (currentPhase d ε t u).re < Real.pi/2 ∧
      (currentPhase d ε t u).im < 0 := by
  obtain ⟨r,hr,h⟩ := current_branch_inclusion d
  refine ⟨r,hr,?_⟩
  intro ε t u hε hεr ht htr hur
  obtain ⟨hre,him⟩ := h ε t u hε hεr ht htr hur
  exact lowerArccos_sheet _ hre him

theorem original_branch_inclusion (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → |u| < r →
      0 < (originalW d ε u).re ∧ 0 < (originalW d ε u).im := by
  obtain ⟨r,hr,h⟩ := current_branch_inclusion d
  exact ⟨r,hr,fun ε u hε hεr hur => h ε 0 u hε hεr le_rfl hr hur⟩

end
end IsingBulk.Branch

