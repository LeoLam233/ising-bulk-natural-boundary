import IsingBulk.Anisotropic.NegativeNormalForm.JointPhaseFactors

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem hyperbolicDivisor_analyticAt (u : ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => hyperbolicDivisor z.1 z.2) (u,0) := by
  exact (Complex.analyticAt_sinh.comp (analyticAt_fst.add analyticAt_snd.div_const)).mul
    ((zeroSlope_analyticAt Complex.analyticAt_sinh).comp_of_eq analyticAt_snd.div_const (by simp))

theorem hyperbolicDivisorSlope_analyticAt (u : ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => hyperbolicDivisorSlope z.1 z.2) (u,0) := by
  have hv : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2/2) (u,0) := analyticAt_snd.div_const
  have hc := (zeroSlope_analyticAt Complex.analyticAt_cosh).comp_of_eq
    hv (show (0:ℂ)/2=0 by simp)
  have hs := (zeroSlope_analyticAt Complex.analyticAt_sinh).comp_of_eq
    hv (show (0:ℂ)/2=0 by simp)
  have hd := (zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_sinh)).comp_of_eq
    hv (show (0:ℂ)/2=0 by simp)
  exact (((Complex.analyticAt_sinh.comp analyticAt_fst).mul hc).mul hs).add
    (((Complex.analyticAt_cosh.comp analyticAt_fst).mul (hs.pow 2))) |>.add
      ((Complex.analyticAt_sinh.comp analyticAt_fst).mul hd)

theorem cosineFirstFactor_analyticAt (B : ℂ → ℂ) (d t : ℂ) (hB : AnalyticAt ℂ B t) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => cosineFirstFactor B d z.1 z.2) (t,0) := by
  have hv : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2) (t,0) := analyticAt_snd
  exact (hB.comp analyticAt_fst).mul
    ((analyticAt_const.mul ((zeroSlope_analyticAt Complex.analyticAt_cos).comp_of_eq hv rfl)).sub
      (analyticAt_const.mul ((zeroSlope_analyticAt Complex.analyticAt_sin).comp_of_eq hv rfl)))

theorem cosineSecondFactor_analyticAt (B : ℂ → ℂ) (d t : ℂ) (hB : AnalyticAt ℂ B t) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => cosineSecondFactor B d z.1 z.2) (t,0) := by
  have hv : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2) (t,0) := analyticAt_snd
  exact (hB.comp analyticAt_fst).mul
    ((analyticAt_const.mul ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_cos)).comp_of_eq hv rfl)).sub
      (analyticAt_const.mul ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_sin)).comp_of_eq hv rfl)))

theorem phase_base_and_increment_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 d) (1-Complex.cos d,0) ∧
    AnalyticAt ℂ (fun z : ℂ × ℂ => phaseIncrement B phi hphi d z.1 z.2) (1-Complex.cos d,0) := by
  have hg := negativePhase_analyticAt_center B phi hphi d hB
  have h0 : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 d) (1-Complex.cos d,0) :=
    hg.comp_of_eq (analyticAt_fst.prod analyticAt_const) rfl
  have h1 : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 (d+z.2)) (1-Complex.cos d,0) :=
    hg.comp_of_eq (analyticAt_fst.prod (analyticAt_const.add analyticAt_snd)) (by simp)
  exact ⟨h0, h1.sub h0⟩

theorem phase_sinh_center_ne_zero (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    Complex.sinh (negativePhase B phi hphi (1-Complex.cos d) d) ≠ 0 := by
  simpa [negativePhase_center, Complex.sinh_mul_I, ← Complex.ofReal_sin] using
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero

theorem phaseFirstFactor_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => phaseFirstFactor B phi hphi d z.1 z.2) (1-Complex.cos d,0) := by
  obtain ⟨h0,hi⟩ := phase_base_and_increment_analyticAt B phi hphi d hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi (1-Complex.cos d) d)).comp_of_eq (h0.prod hi) (by simp [phaseIncrement])
  apply (cosineFirstFactor_analyticAt B d _ hB).div hden
  simpa [phaseIncrement] using phase_sinh_center_ne_zero B phi hphi d

theorem phaseSecondFactor_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => phaseSecondFactor B phi hphi d z.1 z.2) (1-Complex.cos d,0) := by
  obtain ⟨h0,hi⟩ := phase_base_and_increment_analyticAt B phi hphi d hB
  have hs := Complex.analyticAt_sinh.comp h0
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi (1-Complex.cos d) d)).comp_of_eq (h0.prod hi) (by simp [phaseIncrement])
  have hd := (hyperbolicDivisorSlope_analyticAt (negativePhase B phi hphi (1-Complex.cos d) d)).comp_of_eq (h0.prod hi) (by simp [phaseIncrement])
  have hk0 : AnalyticAt ℂ (fun z : ℂ × ℂ => cosineFirstFactor B d z.1 0) (1-Complex.cos d,0) :=
    (cosineFirstFactor_analyticAt B d _ hB).comp_of_eq
    (analyticAt_fst.prod analyticAt_const) (by rfl)
  apply (((cosineSecondFactor_analyticAt B d _ hB).mul hs).sub
    ((hk0.mul (phaseFirstFactor_analyticAt B phi hphi d hB).div_const).mul hd)).div
      (hden.mul hs)
  simpa [phaseIncrement] using mul_ne_zero
    (phase_sinh_center_ne_zero B phi hphi d) (phase_sinh_center_ne_zero B phi hphi d)

end
end IsingBulk.Anisotropic.NegativeNormalForm
