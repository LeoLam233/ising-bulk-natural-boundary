import IsingBulk.Preferred22.Coordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology

/-- On the physical half strip the phase norm is controlled by its sine.
This transfers the proved square-root sine normal form to the actual phase. -/
theorem preferred_phase_norm_le_sine (z : ℂ) (hz : 0≤z.re) (hz' : z.re≤Real.pi/2) :
    ‖z‖ ≤ (Real.pi/2+1)*‖Complex.sin z‖ := by
  have hr : (Complex.sin z).re=Real.sin z.re*Real.cosh z.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  have hi : (Complex.sin z).im=Real.cos z.re*Real.sinh z.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  have hsq : ‖Complex.sin z‖^2=(Real.sin z.re)^2+(Real.sinh z.im)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,hr,hi]
    have ht := Real.sin_sq_add_cos_sq z.re
    have hh := Real.cosh_sq_sub_sinh_sq z.im
    nlinarith [congrArg (fun t : ℝ => t*(Real.sin z.re)^2) hh,
      congrArg (fun t : ℝ => t*(Real.sinh z.im)^2) ht]
  have hs : Real.sin z.re ≤ ‖Complex.sin z‖ := by
    nlinarith [sq_nonneg (Real.sinh z.im),norm_nonneg (Complex.sin z)]
  have hh : |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
    nlinarith [sq_nonneg (Real.sin z.re),norm_nonneg (Complex.sin z),sq_abs (Real.sinh z.im),abs_nonneg (Real.sinh z.im)]
  have hrbound : z.re ≤ (Real.pi/2)*‖Complex.sin z‖ := by
    calc
      z.re = (Real.pi/2)*(2/Real.pi*z.re) := by field_simp
      _ ≤ (Real.pi/2)*Real.sin z.re :=
        mul_le_mul_of_nonneg_left (Real.mul_le_sin hz hz') (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hibound : |z.im| ≤ ‖Complex.sin z‖ := by
    calc
      _ ≤ Real.sinh |z.im| := Real.self_le_sinh_iff.mpr (abs_nonneg _)
      _ = |Real.sinh z.im| := (Real.abs_sinh _).symm
      _ ≤ _ := hh
  calc
    _ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = z.re+|z.im| := by rw [abs_of_nonneg hz]
    _ ≤ (Real.pi/2)*‖Complex.sin z‖+‖Complex.sin z‖ := add_le_add hrbound hibound
    _ = _ := by ring

/-- Actual moving center displacement is O(epsilon), from its proved
source holomorphy and the exact radial parametrization. -/
theorem preferredMovingBranch_radial_bound (d : PreferredBranchData) :
    ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,
      0≤ε → ε<ε₀ →
      ‖preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ)‖ ≤ C*ε := by
  have htrace : AnalyticAt ℂ temperatureTrace (preferredSelectedPoint d) :=
    analyticAt_id.add (analyticAt_id.inv (preferredSelectedPoint_ne_zero d))
  have hB : AnalyticAt ℂ preferredMovingBranch (preferredSelectedPoint d) :=
    (traceMovingBranch_analyticAt_reference d).comp_of_eq htrace (temperatureTrace_preferredSelectedPoint d)
  have hB0 : preferredMovingBranch (preferredSelectedPoint d)=-(d.b:ℂ) := by
    unfold preferredMovingBranch
    rw [temperatureTrace_preferredSelectedPoint,traceMovingBranch_reference]
  obtain ⟨K,U,hU,hLip⟩ := hB.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨(K:ℝ)+1,r,by positivity,hr,?_⟩
  intro ε hε hεr
  have hdist : dist (IsingBulk.Branch.radialParameter d.alpha ε) (preferredSelectedPoint d)=ε := by
    rw [dist_eq_norm]
    have he : IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d=
        (ε:ℂ)*Complex.exp ((d.alpha:ℂ)*Complex.I) := by
      simp only [preferredSelectedPoint,IsingBulk.Branch.radialParameter,add_zero,
        Complex.ofReal_one,one_mul,Complex.ofReal_add]
      ring
    rw [he,norm_mul,Complex.norm_exp]
    simp [Complex.mul_re,Real.norm_eq_abs,abs_of_nonneg hε]
  have hs : IsingBulk.Branch.radialParameter d.alpha ε∈U := hball (by simpa [Metric.mem_ball,hdist] using hεr)
  have hbase : preferredSelectedPoint d∈U := mem_of_mem_nhds hU
  have hh := hLip.dist_le_mul _ hs _ hbase
  rw [hdist,dist_eq_norm,hB0,sub_neg_eq_add] at hh
  exact hh.trans (by nlinarith)

/-- The exact undeformed branch-center coordinate is O(sqrt epsilon).
This is the P=0 anchor needed for the global source coordinate scale. -/
theorem preferred_undeformed_center_coordinate_bound (d : PreferredBranchData) :
    ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,
      0<ε → ε<ε₀ →
      ‖preferredArccos (preferredRadialTrace d ε-Complex.cos (-(d.b:ℂ)))-
        (d.b:ℂ)-preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤
      C*Real.sqrt ε := by
  obtain ⟨c,C,r,hc,hC,hr,hphase⟩ := preferred_outward_branch_control d
  obtain ⟨B,rB,hB,hrB,hbranch⟩ := preferredMovingBranch_radial_bound d
  let R := min r (min rB 1)
  refine ⟨(Real.pi/2+1)*C+B,R,by positivity,lt_min hr (lt_min hrB zero_lt_one),?_⟩
  intro ε hε hεR
  have hεr : ε<r := hεR.trans_le (min_le_left _ _)
  have hεB : ε<rB := hεR.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε<1 := hεR.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_,hsin,_,_,_,hφlo,hφhi,_⟩ := hphase ε 0 0 hε hεr le_rfl hr le_rfl hr
  have hφ := preferred_phase_norm_le_sine (outwardPlateauPhase d ε 0 0) hφlo.le hφhi.le
  have hsin' : ‖Complex.sin (outwardPlateauPhase d ε 0 0)‖≤C*Real.sqrt ε := by simpa using hsin
  have he : outwardPlateauPhase d ε 0 0=
      preferredArccos (preferredRadialTrace d ε-Complex.cos (-(d.b:ℂ))) := by
    unfold outwardPlateauPhase
    rw [outwardPlateauW_formula]
    simp [preferredRadialTrace,outwardPlateauAngle]
  have hεsqrt : ε≤Real.sqrt ε := by nlinarith [Real.sq_sqrt hε.le,Real.sqrt_nonneg ε]
  have hb := hbranch ε hε.le hεB
  calc
    _ = ‖outwardPlateauPhase d ε 0 0-
        (preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ))‖ := by rw [he]; congr 1; ring
    _ ≤ ‖outwardPlateauPhase d ε 0 0‖+
        ‖preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ)‖ := norm_sub_le _ _
    _ ≤ (Real.pi/2+1)*(C*Real.sqrt ε)+B*ε :=
      add_le_add (hφ.trans (mul_le_mul_of_nonneg_left hsin' (by positivity))) hb
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hεsqrt hB.le]

end
end IsingBulk.Preferred22
