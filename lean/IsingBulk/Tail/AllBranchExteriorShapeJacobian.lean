import IsingBulk.Tail.AllBranchExteriorShapeInjective

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

def allBranchExteriorShapeDerivative {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (ω : Fin N → ℝ) (x : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((N:ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
    (∑ i, deriv (originalRealPhase d ε) (x.1+x.2*ω i) •
      ((ContinuousLinearMap.fst ℝ ℝ ℝ)+(ω i) • (ContinuousLinearMap.snd ℝ ℝ ℝ)))

theorem allBranchExterior_shape_map_hasFDerivAt {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a)
    (x : ℝ × ℝ) (hx : x ∈ allBranchExteriorShapeRegion a B.r ω) :
    HasFDerivAt (allBranchExteriorShapeMap d ε ω) (allBranchExteriorShapeDerivative d ε ω x) x := by
  have hi (i : Fin N) : HasFDerivAt (fun y : ℝ × ℝ => originalRealPhase d ε (y.1+y.2*ω i))
      (deriv (originalRealPhase d ε) (x.1+x.2*ω i) •
        ((ContinuousLinearMap.fst ℝ ℝ ℝ)+(ω i) • (ContinuousLinearMap.snd ℝ ℝ ℝ))) x := by
    have hp := (allBranchExterior_realPhase_differentiable B ε (x.1+x.2*ω i) hε hεr
      ((mul_pos B.original.C₀_pos hε).le.trans (ha.trans (hx.2.2.2 i).1)) (hx.2.2.2 i).2).hasDerivAt
    have hl := (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).mul_const (ω i))
    convert! hp.comp_hasFDerivAt x hl using 1
  have hg := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hf := (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul (N:ℝ)
  convert! hf.prodMk hg using 1

theorem allBranchExterior_shape_det {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (ω : Fin N → ℝ) (x : ℝ × ℝ) :
    (allBranchExteriorShapeDerivative d ε ω x).det =
      (N:ℝ)*(∑ i, deriv (originalRealPhase d ε) (x.1+x.2*ω i)*ω i) := by
  apply det_triangular_phase_map _ _ (∑ i, deriv (originalRealPhase d ε) (x.1+x.2*ω i))
  intro y
  simp [allBranchExteriorShapeDerivative,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc,mul_comm]

theorem allBranchExterior_shape_det_lower {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (x : ℝ × ℝ) (hx : x ∈ allBranchExteriorShapeRegion a B.r ω) :
    (N:ℝ)*allBranchExteriorCurvature B*x.2 ≤ |(allBranchExteriorShapeDerivative d ε ω x).det| := by
  have hu : ∀ i, B.original.C₀*ε ≤ x.1+x.2*ω i ∧ x.1+x.2*ω i ≤ B.r :=
    fun i => ⟨ha.trans (hx.2.2.2 i).1,(hx.2.2.2 i).2⟩
  have hh := allBranchExterior_shape_jacobian B ε x.1 x.2 ω hε hεr hx.1.le hzero hunit
    (ha.trans hx.2.1) hx.2.2.1 hu
  have hd := allBranchExterior_shape_hasDerivAt B ε x.1 x.2 ω hε hεr
    (fun i => ⟨(mul_pos B.original.C₀_pos hε).le.trans (hu i).1,(hu i).2⟩)
  simpa only [allBranchExterior_shape_det,hd.deriv] using hh

theorem allBranchExterior_shape_region_measurable {N : ℕ} (a r : ℝ) (ω : Fin N → ℝ) :
    MeasurableSet (allBranchExteriorShapeRegion a r ω) := by
  unfold allBranchExteriorShapeRegion
  measurability

theorem allBranchExterior_shape_image {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a) :
    allBranchExteriorShapeMap d ε ω '' allBranchExteriorShapeRegion a B.r ω ⊆
      Icc (0,0) ((N:ℝ)*B.r,(N:ℝ)*(Real.pi/2)) := by
  rintro _ ⟨x,hx,rfl⟩
  have hxp : 0 ≤ x.1 := (mul_pos B.original.C₀_pos hε).le.trans (ha.trans hx.2.1)
  have hp (i : Fin N) : 0 ≤ originalRealPhase d ε (x.1+x.2*ω i) ∧
      originalRealPhase d ε (x.1+x.2*ω i) ≤ Real.pi/2 := by
    have hu := (hx.2.2.2 i)
    have hpos : 0 ≤ x.1+x.2*ω i := (mul_pos B.original.C₀_pos hε).le.trans (ha.trans hu.1)
    obtain ⟨hr,hi⟩ := B.quadrant ε (x.1+x.2*ω i) hε hεr
      (by simpa [abs_of_nonneg hpos] using hu.2)
    have hh := lowerArccos_sheet _ hr hi
    exact ⟨hh.2.1.le,hh.2.2.1.le⟩
  change (0 ≤ (N:ℝ)*x.1 ∧ 0 ≤ ∑ i, originalRealPhase d ε (x.1+x.2*ω i)) ∧
    (N:ℝ)*x.1 ≤ (N:ℝ)*B.r ∧ (∑ i, originalRealPhase d ε (x.1+x.2*ω i)) ≤ (N:ℝ)*(Real.pi/2)
  refine ⟨⟨by positivity,Finset.sum_nonneg (fun i _ => (hp i).1)⟩,
    mul_le_mul_of_nonneg_left hx.2.2.1 (Nat.cast_nonneg N),?_⟩
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hp i).2)

theorem allBranchExterior_shape_coarea {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (ω : Fin N → ℝ) (hN : 0 < N)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : B.original.C₀*ε ≤ a)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (k : (ℝ × ℝ) → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) :
    IntegrableOn (fun x => x.2*k (allBranchExteriorShapeMap d ε ω x))
      (allBranchExteriorShapeRegion a B.r ω) ∧
    (∫ x in allBranchExteriorShapeRegion a B.r ω, x.2*k (allBranchExteriorShapeMap d ε ω x)) ≤
      ((N:ℝ)*allBranchExteriorCurvature B)⁻¹ *
        (∫ y in Icc (0,0) ((N:ℝ)*B.r,(N:ℝ)*(Real.pi/2)), k y) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hCp := mul_pos hNp (allBranchExterior_curvature_pos B)
  apply injective_weighted_coarea_le (allBranchExterior_shape_region_measurable a B.r ω)
    (allBranchExteriorShapeMap d ε ω) (allBranchExteriorShapeDerivative d ε ω)
    (fun x hx => (allBranchExterior_shape_map_hasFDerivAt B ε a ω hε hεr ha x hx).hasFDerivWithinAt)
    (allBranchExterior_shape_injective B ε a ω hN hε hεr ha hzero hunit)
    (allBranchExterior_shape_image B ε a ω hε hεr ha)
    Prod.snd k continuous_snd.continuousOn hk hk0
    (hk.continuousOn.integrableOn_compact isCompact_Icc) (inv_nonneg.mpr hCp.le)
    (fun x hx => hx.1.le)
  intro x hx
  have hh := allBranchExterior_shape_det_lower B ε a ω hε hεr ha hzero hunit x hx
  have hb := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hCp.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hCp.ne',one_mul] using hb

end
end IsingBulk.Tail
