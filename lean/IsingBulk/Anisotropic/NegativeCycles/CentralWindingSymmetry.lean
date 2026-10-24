import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors
import IsingBulk.Anisotropic.NegativeNormalForm.Hessian
import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm

 theorem negativePhase_neg_angle (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t z : ℂ) :
    negativePhase B phi hphi t (-z)=negativePhase B phi hphi t z := by
  simp [negativePhase,negativeDispersion]

 theorem centralHessian_neg (B : ℂ→ℂ) (phi : ℝ) (d : ℂ) :
    centralHessian B phi (-d)=centralHessian B phi d := by
  simp [centralHessian]

/-- The two genuine minimal winding sectors have the same complex central amplitude. -/
theorem regularResidue_opposite_centers {N : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (Tplus Tminus : Config N→ℂ) (hp : Tplus 0=1-Complex.cos d)
    (hm : Tminus 0=1-Complex.cos (-d)) :
    regularResidue B rootB phi hphi (-d) Tminus 0=
      regularResidue B rootB phi hphi d Tplus 0 := by
  rw [regularResidue_center B rootB phi hphi (-d) (by simpa using hB) Tminus hm,
    regularResidue_center B rootB phi hphi d hB Tplus hp]
  simp

 theorem actual_regularResidue_opposite_centers {N : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (r C : ℝ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (Pplus : UniformProjectedWitness B phi hphi N d r C)
    (Pminus : UniformProjectedWitness B phi hphi N (-d) r C) :
    regularResidue B rootB phi hphi (-d) Pminus.T 0=
      regularResidue B rootB phi hphi d Pplus.T 0 :=
  regularResidue_opposite_centers B rootB phi hphi d hB Pplus.T Pminus.T Pplus.t_zero Pminus.t_zero

/-- The Hessian normalization does not introduce a phase cancellation between the sectors. -/
theorem actual_normalized_centers_add {N : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (r C : ℝ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (Pplus : UniformProjectedWitness B phi hphi N d r C)
    (Pminus : UniformProjectedWitness B phi hphi N (-d) r C) (a : ℕ) :
    regularResidue B rootB phi hphi d Pplus.T 0/(centralHessian B phi d)^a+
      regularResidue B rootB phi hphi (-d) Pminus.T 0/(centralHessian B phi (-d))^a=
      2*(regularResidue B rootB phi hphi d Pplus.T 0/(centralHessian B phi d)^a) := by
  rw [actual_regularResidue_opposite_centers B rootB phi hphi d r C hB Pplus Pminus,centralHessian_neg]
  ring

end IsingBulk.Anisotropic.NegativeCycles
