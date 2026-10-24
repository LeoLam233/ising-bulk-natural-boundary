import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy

/-! Actual simple-pole subtraction for the resonant coth kernel. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

def cothHalf (F : ℂ → ℂ) (t : ℂ) : ℂ :=
  Complex.cosh (F t/2) / Complex.sinh (F t/2)

def regularCothResidue (F : ℂ → ℂ) (T t : ℂ) : ℂ :=
  Complex.cosh (F t/2) / dslope (fun u => Complex.sinh (F u/2)) T t

theorem sinhHalf_hasDerivAt {F : ℂ → ℂ} {T : ℂ} (hF : AnalyticAt ℂ F T) (h0 : F T=0) :
    HasDerivAt (fun t => Complex.sinh (F t/2)) (deriv F T/2) T := by
  have h := (Complex.hasDerivAt_sinh (F T/2)).comp T (hF.differentiableAt.hasDerivAt.div_const 2)
  convert h using 1 <;> simp [h0, Function.comp_def]

theorem regularCothResidue_center {F : ℂ → ℂ} {T : ℂ} (hF : AnalyticAt ℂ F T) (h0 : F T=0) :
    regularCothResidue F T T = 2/deriv F T := by
  simp only [regularCothResidue, dslope_same, (sinhHalf_hasDerivAt hF h0).deriv,
    h0, zero_div, Complex.cosh_zero]
  ring

theorem regularCothResidue_analyticAt {F : ℂ → ℂ} {T : ℂ}
    (hF : AnalyticAt ℂ F T) (h0 : F T=0) (hd : deriv F T ≠ 0) :
    AnalyticAt ℂ (regularCothResidue F T) T := by
  apply (Complex.analyticAt_cosh.comp hF.div_const).div
    (analyticAt_dslope_center (Complex.analyticAt_sinh.comp hF.div_const))
  rw [dslope_same]
  change deriv (fun t => Complex.sinh (F t/2)) T ≠ 0
  rw [(sinhHalf_hasDerivAt hF h0).deriv]
  exact div_ne_zero hd (by norm_num)

/-- Equality on the punctured neighborhood, not just a formal residue value. -/
theorem cothHalf_eq_regular_div {F : ℂ → ℂ} {T t : ℂ} (h0 : F T=0) (ht : t ≠ T) :
    cothHalf F t = regularCothResidue F T t / (t-T) := by
  have h := sub_smul_dslope (fun u => Complex.sinh (F u/2)) T t
  simp only [h0, zero_div, Complex.sinh_zero, sub_zero, smul_eq_mul] at h
  unfold cothHalf regularCothResidue
  rw [← h]
  field_simp

/-- The full analytic numerator times the actual coth kernel has an analytic
remainder after the exact simple pole is subtracted. -/
theorem exists_analytic_coth_subtraction {F N : ℂ → ℂ} {T : ℂ}
    (hF : AnalyticAt ℂ F T) (hN : AnalyticAt ℂ N T) (h0 : F T=0)
    (hd : deriv F T ≠ 0) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A T ∧
      ∀ t : ℂ, t ≠ T →
        N t*cothHalf F t = (2*N T/deriv F T)/(t-T)+A t := by
  let R : ℂ → ℂ := fun t => N t*regularCothResidue F T t
  have hR : AnalyticAt ℂ R T := hN.mul (regularCothResidue_analyticAt hF h0 hd)
  refine ⟨dslope R T, analyticAt_dslope_center hR, ?_⟩
  intro t ht
  have h := sub_smul_dslope R T t
  simp only [smul_eq_mul] at h
  have hRT : R T = 2*N T/deriv F T := by
    dsimp [R]
    rw [regularCothResidue_center hF h0]
    ring
  rw [cothHalf_eq_regular_div h0 ht]
  have hne : t-T ≠ 0 := sub_ne_zero.mpr ht
  rw [hRT] at h
  dsimp only [R] at *
  field_simp [hd] at h
  field_simp
  linear_combination -h

end
end IsingBulk.Anisotropic.NegativeNormalForm
