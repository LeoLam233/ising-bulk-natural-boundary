import IsingBulk.Anisotropic.NegativeNormalForm.JointEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarNormalForm

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

def phaseEnergy (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d t v : ℂ) : ℂ :=
  energyQuotient (negativePhase B phi hphi t) (deriv (negativePhase B phi hphi t) d)
    d (centralHessian B phi d) (phaseParameterQuotient B phi hphi d t) v

theorem phaseEnergy_center (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) : phaseEnergy B phi hphi d (1-Complex.cos d) 0=1 := by
  unfold phaseEnergy
  rw [phaseParameterQuotient_center B phi hphi d hB]
  exact centralEnergy_zero B phi hphi d hh hBn

theorem phaseEnergy_analyticAt (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => phaseEnergy B phi hphi d z.1 z.2) (1-Complex.cos d,0) := by
  apply energyQuotient_joint_analyticAt B phi hphi d _ hB _
    (phaseParameterQuotient_analyticAt B phi hphi d hB)
  rw [phaseParameterQuotient_center B phi hphi d hB]
  exact centralParameterSlope_ne_zero B phi hphi d hBn

theorem sqrt_analyticAt_one : AnalyticAt ℂ Complex.sqrt 1 := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
  exact Complex.differentiableAt_sqrt hz

/-- The actual parameter-dependent square root is analytic, not just its central slice. -/
theorem phaseRootEnergy_analyticAt (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.sqrt (phaseEnergy B phi hphi d z.1 z.2)) (1-Complex.cos d,0) :=
  sqrt_analyticAt_one.comp_of_eq (phaseEnergy_analyticAt B phi hphi d hB hBn)
    (phaseEnergy_center B phi hphi d hB hBn hh)

theorem phaseSeparableMap_along_pole_analyticAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d) :
    AnalyticAt ℂ (fun v => phaseSeparableMap B phi hphi d (T v) v) 0 := by
  apply analyticAt_pi_iff.mpr
  intro i
  have hi := (ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt 0
  exact hi.mul ((phaseRootEnergy_analyticAt B phi hphi d hB hBn hh).comp_of_eq
    (hT.prod hi) (by simp [hT0]))

/-- Dependence of the pole parameter contributes no linear term, because each
coordinate carries its actual vanishing angular factor. -/
theorem phaseSeparableMap_along_pole_hasFDerivAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d) :
    HasFDerivAt (fun v => phaseSeparableMap B phi hphi d (T v) v)
      (ContinuousLinearMap.id ℂ (Config n)) 0 := by
  let S : Config n → Config n := fun v i => Complex.sqrt (phaseEnergy B phi hphi d (T v) (v i))
  have hS : AnalyticAt ℂ S 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (phaseRootEnergy_analyticAt B phi hphi d hB hBn hh).comp_of_eq
      (hT.prod ((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt 0)) (by simp [hT0])
  have hS0 : S 0=1 := by
    ext i
    simp [S,hT0,phaseEnergy_center B phi hphi d hB hBn hh]
  have hd := (hasFDerivAt_id (𝕜 := ℂ) (0:Config n)).mul hS.differentiableAt.hasFDerivAt
  convert! hd using 1
  simp [hS0]


end
end IsingBulk.Anisotropic.NegativeNormalForm
