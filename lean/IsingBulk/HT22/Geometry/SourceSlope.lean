import IsingBulk.HT22.Geometry.ReciprocalCone

/-! The inverse-slope source has one reciprocal sine, not the inverse cube
occurring in scalar coarea. Its remaining multiplier tends to one at the
actual branch point. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter
open IsingBulk.Preferred22

def sourceInverseSlopeNumerator (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  Complex.cos (outwardPlateauAngle d δ u)*(1-(outwardPlateauW d ε δ u)^2)+
  (Complex.sin (outwardPlateauAngle d δ u))^2*outwardPlateauW d ε δ u

def sourceInverseSlopeFactor (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  sourceInverseSlopeNumerator d ε δ u /
    (Complex.sin (outwardPlateauPhase d ε δ u)-
      Complex.sin (outwardPlateauAngle d δ u))^2

def sourceInverseSlopeDerivative (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  sourceInverseSlopeFactor d ε δ u / Complex.sin (outwardPlateauPhase d ε δ u)

theorem outwardW_zero (d : PreferredBranchData) : outwardPlateauW d 0 0 0 = 1 := by
  have h := outwardPlateauW_transfer d 0 0 0
  simpa only [mul_zero, add_zero, IsingBulk.Branch.currentW_zero] using h.symm

theorem outwardSine_sqrt (d : PreferredBranchData) (ε δ u : ℝ) :
    Complex.sin (outwardPlateauPhase d ε δ u) =
      Complex.sqrt (1-(outwardPlateauW d ε δ u)^2) := by
  exact IsingBulk.Branch.sin_lowerArccos _

theorem outwardSine_zero (d : PreferredBranchData) :
    Complex.sin (outwardPlateauPhase d 0 0 0) = 0 := by
  rw [outwardSine_sqrt, outwardW_zero]
  norm_num

theorem outwardW_continuous (d : PreferredBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ => outwardPlateauW d z.1 z.2.1 z.2.2) 0 := by
  unfold outwardPlateauW IsingBulk.Branch.plateauW IsingBulk.Branch.radialParameter
  fun_prop (disch := simp [Complex.exp_ne_zero])

theorem outwardSine_continuous (d : PreferredBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      Complex.sin (outwardPlateauPhase d z.1 z.2.1 z.2.2)) 0 := by
  simp_rw [outwardSine_sqrt]
  have hi : ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      1-(outwardPlateauW d z.1 z.2.1 z.2.2)^2) 0 :=
    ((outwardW_continuous d).pow 2).const_sub 1
  exact (Complex.continuousAt_sqrt (by simp [outwardW_zero])).comp hi

theorem sourceInverseSlopeFactor_zero (d : PreferredBranchData) :
    sourceInverseSlopeFactor d 0 0 0 = 1 := by
  have hs : (Real.sin d.b:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt))
  simp [sourceInverseSlopeFactor, sourceInverseSlopeNumerator, outwardW_zero,
    outwardSine_zero, outwardPlateauAngle, Complex.sin_neg, ← Complex.ofReal_sin,
    hs]

theorem sourceInverseSlopeFactor_continuous (d : PreferredBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      sourceInverseSlopeFactor d z.1 z.2.1 z.2.2) 0 := by
  have hW := outwardW_continuous d
  have hsin := outwardSine_continuous d
  have ha : ContinuousAt (fun z : ℝ × ℝ × ℝ => outwardPlateauAngle d z.2.1 z.2.2) 0 := by
    unfold outwardPlateauAngle
    fun_prop
  have hn : ContinuousAt (fun z : ℝ × ℝ × ℝ =>
      sourceInverseSlopeNumerator d z.1 z.2.1 z.2.2) 0 :=
    ((Complex.continuous_cos.continuousAt.comp ha).mul ((hW.pow 2).const_sub 1)).add (((Complex.continuous_sin.continuousAt.comp ha).pow 2).mul hW)
  apply hn.div ((hsin.sub (Complex.continuous_sin.continuousAt.comp ha)).pow 2)
  have hs : (Real.sin d.b:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt))
  simp [outwardSine_zero, outwardPlateauAngle, Complex.sin_neg, ← Complex.ofReal_sin, hs]

theorem sourceInverseSlopeFactor_small (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ, |ε| < r → |δ| < r → |u| < r →
      ‖sourceInverseSlopeFactor d ε δ u-1‖ ≤ (1/4:ℝ) := by
  have he : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 0,
      ‖sourceInverseSlopeFactor d z.1 z.2.1 z.2.2-1‖ < (1/4:ℝ) := by
    apply ((sourceInverseSlopeFactor_continuous d).sub_const 1).norm.eventually_lt continuousAt_const
    simp [sourceInverseSlopeFactor_zero]
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro ε δ u hε hδ hu
  apply (hball (y := (ε,δ,u)) ?_).le
  simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using
    And.intro hε (And.intro hδ hu)

/-- Protected first-reciprocal projection for the literal source expression,
on both signs of u, uniformly including δ=0. -/
theorem sourceInverseSlope_projection (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      (1/4:ℝ)*‖(Complex.sin (outwardPlateauPhase d ε δ u))⁻¹‖ ≤
        (covarianceDirection*sourceInverseSlopeDerivative d ε δ u).re := by
  obtain ⟨_,_,r₁,_,_,hr₁,hsource⟩ := outward_sine_all_signs d
  obtain ⟨r₂,hr₂,hfactor⟩ := sourceInverseSlopeFactor_small d
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  intro ε δ u hε hεr hδ hδr hu
  obtain ⟨_,_,hsr,hsi⟩ := hsource ε δ u hε
    (hεr.trans_le (min_le_left _ _)) hδ (hδr.trans_le (min_le_left _ _))
    (hu.trans_le (min_le_left _ _))
  have hf := hfactor ε δ u
    (by simpa [abs_of_pos hε] using hεr.trans_le (min_le_right r₁ r₂))
    (by simpa [abs_of_nonneg hδ] using hδr.trans_le (min_le_right r₁ r₂))
    (hu.trans_le (min_le_right _ _))
  have hh := IsingBulk.HT22.projected_multiplier_stability
    (phase := covarianceDirection) (z := (Complex.sin (outwardPlateauPhase d ε δ u))⁻¹)
    (by rw [covarianceDirection_norm]) hf (first_reciprocal_cone _ hsr.le hsi.le)
  norm_num only [show (1/2:ℝ)-1/4=1/4 by norm_num] at hh
  simpa only [sourceInverseSlopeDerivative, div_eq_mul_inv] using hh

/-- The literal angular representation of the inverse's v partial. -/
def sourceInverseSlopeValue (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  Complex.sin (outwardPlateauPhase d ε δ u) /
    (Complex.sin (outwardPlateauPhase d ε δ u)-Complex.sin (outwardPlateauAngle d δ u))

theorem sourceInverseSlope_hasDerivAt (d : PreferredBranchData) (ε δ u : ℝ)
    (hwr : 0 < (outwardPlateauW d ε δ u).re)
    (hwi : 0 < (outwardPlateauW d ε δ u).im)
    (hs : Complex.sin (outwardPlateauPhase d ε δ u) ≠ 0)
    (hden : Complex.sin (outwardPlateauPhase d ε δ u)-
      Complex.sin (outwardPlateauAngle d δ u) ≠ 0) :
    HasDerivAt (sourceInverseSlopeValue d ε δ)
      (sourceInverseSlopeDerivative d ε δ u) u := by
  have hphi := outwardPlateauPhase_hasDerivAt d ε δ u hwr hwi
  have hang : HasDerivAt (outwardPlateauAngle d δ) (1:ℂ) u := by
    have h := (((hasDerivAt_id u).const_add (-d.b)).ofReal_comp).sub_const (Complex.I*(δ:ℂ))
    convert! h using 1
  have hsinphi := (Complex.hasDerivAt_sin _).scomp u hphi
  have hsinang := (Complex.hasDerivAt_sin _).scomp u hang
  have hquot := hsinphi.div (hsinphi.sub hsinang) hden
  have hsq := Complex.sin_sq_add_cos_sq (outwardPlateauPhase d ε δ u)
  rw [outwardPlateauPhase_cos] at hsq
  convert hquot using 1
  · rfl
  · dsimp only [sourceInverseSlopeDerivative, sourceInverseSlopeFactor,
      sourceInverseSlopeNumerator]
    simp only [smul_eq_mul, one_mul, Function.comp_apply, Pi.sub_apply, outwardPlateauPhase_cos]
    field_simp [hs, hden]
    linear_combination -(Complex.cos (outwardPlateauAngle d δ u))*hsq

/-- A genuine lower bound at first-reciprocal scale on both sides of the
branch. Constants are chosen before all three varying coordinates. -/
theorem sourceInverseSlope_lower (d : PreferredBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      c/Real.sqrt (|u|+ε+δ) ≤
        (covarianceDirection*sourceInverseSlopeDerivative d ε δ u).re := by
  obtain ⟨_,C,r₁,_,hC,hr₁,hsource⟩ := outward_sine_all_signs d
  obtain ⟨r₂,hr₂,hproj⟩ := sourceInverseSlope_projection d
  refine ⟨1/(4*C), min r₁ r₂, by positivity, lt_min hr₁ hr₂, ?_⟩
  intro ε δ u hε hεr hδ hδr hu
  obtain ⟨_,hupper,hsr,_⟩ := hsource ε δ u hε
    (hεr.trans_le (min_le_left _ _)) hδ (hδr.trans_le (min_le_left _ _))
    (hu.trans_le (min_le_left _ _))
  have hh := hproj ε δ u hε (hεr.trans_le (min_le_right _ _)) hδ
    (hδr.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _))
  have hs : Complex.sin (outwardPlateauPhase d ε δ u) ≠ 0 := by
    intro hz
    rw [hz,Complex.zero_re] at hsr
    exact (lt_irrefl 0) hsr
  have hn : 0 < ‖Complex.sin (outwardPlateauPhase d ε δ u)‖ := norm_pos_iff.mpr hs
  have hL : 0 < Real.sqrt (|u|+ε+δ) := Real.sqrt_pos.mpr (by positivity)
  have hi : 1/(C*Real.sqrt (|u|+ε+δ)) ≤
      1/‖Complex.sin (outwardPlateauPhase d ε δ u)‖ :=
    one_div_le_one_div_of_le hn hupper
  rw [norm_inv, inv_eq_one_div] at hh
  calc
    1/(4*C)/Real.sqrt (|u|+ε+δ) = (1/4:ℝ)*(1/(C*Real.sqrt (|u|+ε+δ))) := by ring
    _ ≤ (1/4:ℝ)*(1/‖Complex.sin (outwardPlateauPhase d ε δ u)‖) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ _ := hh

theorem sourceInverseSlope_denominator_bound (d : PreferredBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      |ε| < r → |δ| < r → |u| < r →
      Complex.sin (outwardPlateauPhase d ε δ u)-
        Complex.sin (outwardPlateauAngle d δ u) ≠ 0 ∧
      ‖(Complex.sin (outwardPlateauPhase d ε δ u)-
        Complex.sin (outwardPlateauAngle d δ u))⁻¹‖ ≤ C := by
  let F := fun z : ℝ × ℝ × ℝ => Complex.sin (outwardPlateauPhase d z.1 z.2.1 z.2.2)-
    Complex.sin (outwardPlateauAngle d z.2.1 z.2.2)
  have hF : ContinuousAt F 0 := by
    apply (outwardSine_continuous d).sub
    apply Complex.continuous_sin.continuousAt.comp
    unfold outwardPlateauAngle
    fun_prop
  have h0 : F 0 ≠ 0 := by
    have hs : (Real.sin d.b:ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt))
    simp [F, outwardSine_zero, outwardPlateauAngle, Complex.sin_neg, ← Complex.ofReal_sin, hs]
  let C := ‖(F 0)⁻¹‖+1
  have hC : 0 < C := by dsimp [C]; positivity
  have he : ∀ᶠ z in 𝓝 (0:ℝ × ℝ × ℝ), F z ≠ 0 ∧ ‖(F z)⁻¹‖ < C := by
    filter_upwards [hF.eventually_ne h0,
      (hF.inv₀ h0).norm.eventually_lt
        (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => C) 0) (by dsimp [C]; linarith)] with z hz hn
    exact ⟨hz,hn⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C,r,hC,hr,?_⟩
  intro ε δ u hε hδ hu
  have hz : dist (ε,δ,u) (0:ℝ × ℝ × ℝ) < r := by
    simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using
      And.intro hε (And.intro hδ hu)
  exact ⟨(hball hz).1,(hball hz).2.le⟩

/-- The regular inverse slope vanishes at square-root scale uniformly even
on the negative sliver; no positive lower bound on δ/ε is needed. -/
theorem sourceInverseSlope_upper (d : PreferredBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      ‖sourceInverseSlopeValue d ε δ u‖ ≤ C*Real.sqrt (|u|+ε+δ) := by
  obtain ⟨_,C₁,r₁,_,hC₁,hr₁,hsource⟩ := outward_sine_all_signs d
  obtain ⟨C₂,r₂,hC₂,hr₂,hden⟩ := sourceInverseSlope_denominator_bound d
  refine ⟨C₁*C₂,min r₁ r₂,mul_pos hC₁ hC₂,lt_min hr₁ hr₂,?_⟩
  intro ε δ u hε hεr hδ hδr hu
  have hupp := (hsource ε δ u hε (hεr.trans_le (min_le_left _ _)) hδ
    (hδr.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))).2.1
  have hd := (hden ε δ u
    (by simpa [abs_of_pos hε] using hεr.trans_le (min_le_right r₁ r₂))
    (by simpa [abs_of_nonneg hδ] using hδr.trans_le (min_le_right r₁ r₂))
    (hu.trans_le (min_le_right _ _))).2
  rw [sourceInverseSlopeValue, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (C₁*Real.sqrt (|u|+ε+δ))*C₂ :=
      mul_le_mul hupp hd (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end IsingBulk.HT22.Geometry
