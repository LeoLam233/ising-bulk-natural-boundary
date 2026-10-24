import IsingBulk.Anisotropic.NegativeNormalForm.JointPhaseIdentity

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

/-- Three scalar variables (t,d,v), before any particle number is chosen. -/
abbrev ScalarTriple := ℂ × (ℂ × ℂ)

theorem cosineFirstFactor_triple_analyticAt (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => cosineFirstFactor B p.2.1 p.1 p.2.2) 0 := by
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hd : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hv : AnalyticAt ℂ (fun p : ScalarTriple => p.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  exact (hB.fun_comp_of_eq (f := fun p : ScalarTriple => p.1) ht rfl).mul
    (((Complex.analyticAt_cos.comp hd).mul ((zeroSlope_analyticAt Complex.analyticAt_cos).fun_comp_of_eq (f := fun p : ScalarTriple => p.2.2) hv rfl)).sub
      ((Complex.analyticAt_sin.comp hd).mul ((zeroSlope_analyticAt Complex.analyticAt_sin).fun_comp_of_eq (f := fun p : ScalarTriple => p.2.2) hv rfl)))

theorem cosineSecondFactor_triple_analyticAt (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => cosineSecondFactor B p.2.1 p.1 p.2.2) 0 := by
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hd : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hv : AnalyticAt ℂ (fun p : ScalarTriple => p.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  exact (hB.fun_comp_of_eq (f := fun p : ScalarTriple => p.1) ht rfl).mul
    (((Complex.analyticAt_cos.comp hd).mul
      ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_cos)).fun_comp_of_eq (f := fun p : ScalarTriple => p.2.2) hv rfl)).sub
      ((Complex.analyticAt_sin.comp hd).mul
        ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_sin)).fun_comp_of_eq (f := fun p : ScalarTriple => p.2.2) hv rfl)))

theorem phase_base_increment_triple_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => negativePhase B phi hphi p.1 p.2.1) 0 ∧
    AnalyticAt ℂ (fun p : ScalarTriple => phaseIncrement B phi hphi p.2.1 p.1 p.2.2) 0 := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hd : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hv : AnalyticAt ℂ (fun p : ScalarTriple => p.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  have h0 : AnalyticAt ℂ (fun p : ScalarTriple => negativePhase B phi hphi p.1 p.2.1) 0 :=
    hg.fun_comp_of_eq (f := fun p : ScalarTriple => (p.1,p.2.1)) (ht.prod hd) rfl
  have h1 : AnalyticAt ℂ (fun p : ScalarTriple => negativePhase B phi hphi p.1 (p.2.1+p.2.2)) 0 :=
    hg.fun_comp_of_eq (f := fun p : ScalarTriple => (p.1,p.2.1+p.2.2)) (ht.prod (hd.add hv)) (by simp)
  exact ⟨h0,h1.sub h0⟩

theorem phaseFirstFactor_triple_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2) 0 := by
  obtain ⟨h0,hi⟩ := phase_base_increment_triple_analyticAt B phi hphi hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi 0 0)).fun_comp_of_eq
    (f := fun p : ScalarTriple => (negativePhase B phi hphi p.1 p.2.1,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2)) (h0.prod hi) (by simp [phaseIncrement])
  apply (cosineFirstFactor_triple_analyticAt B hB).div hden
  simpa [phaseIncrement] using phase_sinh_center_ne_zero B phi hphi 0

theorem phaseSecondFactor_triple_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2) 0 := by
  obtain ⟨h0,hi⟩ := phase_base_increment_triple_analyticAt B phi hphi hB
  have hs := Complex.analyticAt_sinh.comp h0
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi 0 0)).fun_comp_of_eq
    (f := fun p : ScalarTriple => (negativePhase B phi hphi p.1 p.2.1,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2)) (h0.prod hi) (by simp [phaseIncrement])
  have hd := (hyperbolicDivisorSlope_analyticAt (negativePhase B phi hphi 0 0)).fun_comp_of_eq
    (f := fun p : ScalarTriple => (negativePhase B phi hphi p.1 p.2.1,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2)) (h0.prod hi) (by simp [phaseIncrement])
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hdelta : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hk0 : AnalyticAt ℂ (fun p : ScalarTriple => cosineFirstFactor B p.2.1 p.1 0) 0 :=
    (cosineFirstFactor_triple_analyticAt B hB).fun_comp_of_eq
      (f := fun p : ScalarTriple => (p.1,p.2.1,0)) (ht.prod (hdelta.prod analyticAt_const)) rfl
  apply (((cosineSecondFactor_triple_analyticAt B hB).mul hs).sub
    ((hk0.mul (phaseFirstFactor_triple_analyticAt B phi hphi hB).div_const).mul hd)).div
      (hden.mul hs)
  simpa [phaseIncrement] using mul_ne_zero
    (phase_sinh_center_ne_zero B phi hphi 0) (phase_sinh_center_ne_zero B phi hphi 0)

end
end IsingBulk.Anisotropic.NegativeNormalForm
