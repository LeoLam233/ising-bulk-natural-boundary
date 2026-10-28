import IsingBulk.HT22.Geometry.SourceSlope

/-! Literal canonical Uv on the actual lower-branch source, with the branch
strip established uniformly from the reference geometry. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter
open IsingBulk.Preferred22

theorem outwardPhase_zero (d : PreferredBranchData) : outwardPlateauPhase d 0 0 0 = 0 := by
  simp [outwardPlateauPhase, preferredArccos, preferredCosineRoot, outwardW_zero]

theorem outwardPhase_continuous (d : PreferredBranchData) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ => outwardPlateauPhase d z.1 z.2.1 z.2.2) 0 := by
  have hr := (outwardW_continuous d).add ((outwardSine_continuous d).const_mul Complex.I)
  have hl := hr.clog (by simp [outwardW_zero, outwardSine_zero])
  convert hl.const_mul (-Complex.I) using 1
  funext z
  change outwardPlateauPhase d z.1 z.2.1 z.2.2 =
    -Complex.I*Complex.log (outwardPlateauW d z.1 z.2.1 z.2.2+
      Complex.I*Complex.sin (outwardPlateauPhase d z.1 z.2.1 z.2.2))
  rw [outwardSine_sqrt]
  rfl

theorem outward_source_strip (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ, |ε| < r → |δ| < r → |u| < r →
      Complex.cos ((outwardPlateauAngle d δ u+outwardPlateauPhase d ε δ u)/2) ≠ 0 ∧
      0 < ((outwardPlateauPhase d ε δ u-outwardPlateauAngle d δ u)/2).re ∧
      ((outwardPlateauPhase d ε δ u-outwardPlateauAngle d δ u)/2).re < Real.pi := by
  have ha : ContinuousAt (fun z : ℝ × ℝ × ℝ => outwardPlateauAngle d z.2.1 z.2.2) 0 := by
    unfold outwardPlateauAngle
    fun_prop
  have hp := outwardPhase_continuous d
  have hh := Complex.continuous_re.continuousAt.comp ((hp.sub ha).div_const 2)
  have hc := Complex.continuous_cos.continuousAt.comp ((ha.add hp).div_const 2)
  have he : ((outwardPlateauPhase d 0 0 0-outwardPlateauAngle d 0 0)/2).re = d.b/2 := by
    simp [outwardPhase_zero, outwardPlateauAngle ]
  have hn : Complex.cos ((outwardPlateauAngle d 0 0+outwardPlateauPhase d 0 0 0)/2) ≠ 0 := by
    have hcos : Real.cos (-d.b/2) ≠ 0 := (Real.cos_pos_of_mem_Ioo
      (show -(Real.pi/2) < -d.b/2 ∧ -d.b/2 < Real.pi/2 by
        constructor <;> linarith [d.b_pos, d.b_lt, Real.pi_pos])).ne'
    convert Complex.ofReal_ne_zero.mpr hcos using 1
    simp only [outwardPhase_zero, outwardPlateauAngle, add_zero, mul_zero,
      sub_zero, Complex.ofReal_zero, Complex.ofReal_neg]
    push_cast
    rfl
  have hevent : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 0,
      Complex.cos ((outwardPlateauAngle d z.2.1 z.2.2+outwardPlateauPhase d z.1 z.2.1 z.2.2)/2) ≠ 0 ∧
      0 < ((outwardPlateauPhase d z.1 z.2.1 z.2.2-outwardPlateauAngle d z.2.1 z.2.2)/2).re ∧
      ((outwardPlateauPhase d z.1 z.2.1 z.2.2-outwardPlateauAngle d z.2.1 z.2.2)/2).re < Real.pi := by
    filter_upwards [hc.eventually_ne hn,
      (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => (0:ℝ)) 0).eventually_lt hh
        (by change 0 < ((outwardPlateauPhase d 0 0 0-outwardPlateauAngle d 0 0)/2).re; rw [he]; linarith [d.b_pos]),
      hh.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => Real.pi) 0)
        (by change ((outwardPlateauPhase d 0 0 0-outwardPlateauAngle d 0 0)/2).re < Real.pi; rw [he]; linarith [d.b_lt, Real.pi_pos])]
      with z hz hl hu
    exact ⟨hz,hl,hu⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r,hr,?_⟩
  intro ε δ u hε hδ hu
  apply hball (y := (ε,δ,u))
  simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using
    And.intro hε (And.intro hδ hu)

theorem inverseV_source_ratio (t w φ : ℂ)
    (hdisp : Complex.cos w+Complex.cos φ=temperatureTrace t)
    (hc : Complex.cos ((w+φ)/2) ≠ 0)
    (hl : 0 < ((φ-w)/2).re) (hu : ((φ-w)/2).re < Real.pi)
    (hs : Complex.sin φ ≠ 0) :
    inverseV t (w+φ) = Complex.sin φ/(Complex.sin φ-Complex.sin w) := by
  have he : regularInverse t (w+φ) = w :=
    complexRightInverse_inverse _ _ _ hdisp hc hl hu
  have hp : regularPhase t (w+φ) = φ := by simp [regularPhase,he]
  have hU := regularInverse_analyticAt_of_strip t w φ hdisp hc hl hu
  have hd := regularInverse_derivative t (w+φ) hc hU (by simpa only [hp] using hs)
  simpa only [inverseV, continuedRoot, he, hp] using hd

def sourceInverseV (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  inverseV (IsingBulk.Branch.radialParameter d.alpha ε)
    (sumCoordinate (IsingBulk.Branch.radialParameter d.alpha ε) (outwardPlateauAngle d δ u))

theorem source_physicalPhase (d : PreferredBranchData) (ε δ u : ℝ) :
    physicalPhase (IsingBulk.Branch.radialParameter d.alpha ε) (outwardPlateauAngle d δ u) =
      outwardPlateauPhase d ε δ u := by
  simp only [physicalPhase, temperatureTrace, outwardPlateauPhase, outwardPlateauW_formula]

theorem sourceInverseV_eq_ratio (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      sourceInverseV d ε δ u = sourceInverseSlopeValue d ε δ u := by
  obtain ⟨r₁,hr₁,hstrip⟩ := outward_source_strip d
  obtain ⟨_,_,r₂,_,_,hr₂,hsine⟩ := outward_sine_all_signs d
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro ε δ u hε hεr hδ hδr hu
  obtain ⟨hc,hl,hh⟩ := hstrip ε δ u
    (by simpa [abs_of_pos hε] using hεr.trans_le (min_le_left r₁ r₂))
    (by simpa [abs_of_nonneg hδ] using hδr.trans_le (min_le_left r₁ r₂))
    (hu.trans_le (min_le_left _ _))
  obtain ⟨_,_,hsr,_⟩ := hsine ε δ u hε (hεr.trans_le (min_le_right _ _)) hδ
    (hδr.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _))
  have hs : Complex.sin (outwardPlateauPhase d ε δ u) ≠ 0 := by
    intro hz
    rw [hz,Complex.zero_re] at hsr
    exact (lt_irrefl 0) hsr
  unfold sourceInverseV sumCoordinate
  rw [source_physicalPhase]
  apply inverseV_source_ratio _ _ _ ?_ hc hl hh hs
  rw [outwardPlateauPhase_cos, outwardPlateauW_formula]
  simp only [temperatureTrace]
  ring

end
end IsingBulk.HT22.Geometry
