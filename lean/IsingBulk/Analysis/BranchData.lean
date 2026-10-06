import IsingBulk.Analysis.BranchRadial
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Fixed source data and the actual radial original/current branches.
No quantitative estimate is a field of the setup. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

structure LocalBranchData where
  theta : ℝ
  thetaB : ℝ
  c₀ : ℝ
  tau : ℝ
  alpha : ℝ
  theta_pos : 0 < theta
  theta_lt : theta < Real.pi/2
  thetaB_pos : 0 < thetaB
  thetaB_lt : thetaB < Real.pi
  angle_relation : Real.cos thetaB = 2*Real.cos theta-1
  c₀_pos : 0 < c₀
  margin : 0 < 2*Real.sin theta-c₀*Real.sin thetaB
  tau_pos : 0 < tau
  alpha_pos : 0 < alpha

def LocalBranchData.a (d : LocalBranchData) : ℝ := Real.sin d.thetaB
def LocalBranchData.b (d : LocalBranchData) : ℝ := 2*Real.sin d.theta-d.c₀*d.a

theorem LocalBranchData.a_pos (d : LocalBranchData) : 0 < d.a :=
  Real.sin_pos_of_pos_of_lt_pi d.thetaB_pos d.thetaB_lt
theorem LocalBranchData.b_pos (d : LocalBranchData) : 0 < d.b := d.margin

def currentW (d : LocalBranchData) (ε t u : ℝ) : ℂ :=
  plateauW (radialParameter d.theta ε) (-d.c₀*ε+d.tau*t/2) d.thetaB (u:ℂ)
def currentD (d : LocalBranchData) (ε t u : ℝ) : ℂ := 1-currentW d ε t u
def currentPhase (d : LocalBranchData) (ε t u : ℝ) : ℂ := lowerArccos (currentW d ε t u)
def originalW (d : LocalBranchData) (ε u : ℝ) : ℂ := currentW d ε 0 u
def originalD (d : LocalBranchData) (ε u : ℝ) : ℂ := currentD d ε 0 u
def originalPhase (d : LocalBranchData) (ε u : ℝ) : ℂ := currentPhase d ε 0 u
def originalRealPhase (d : LocalBranchData) (ε u : ℝ) : ℝ := (originalPhase d ε u).re

theorem currentW_dispersion (d : LocalBranchData) (ε t u : ℝ) :
    currentW d ε t u = dispersion (radialParameter d.theta ε)
      (plateauY d.c₀ ε d.tau t d.thetaB u) :=
  plateauW_eq_dispersion _ _ _ _ _ _ _

theorem originalW_dispersion (d : LocalBranchData) (ε u : ℝ) :
    originalW d ε u = dispersion (radialParameter d.theta ε)
      (Complex.exp ((-d.c₀*ε:ℝ)+((-d.thetaB+u:ℝ):ℂ)*Complex.I)) := by
  rw [originalW,currentW_dispersion]
  simp [plateauY]

theorem current_components (d : LocalBranchData) (ε t u : ℝ) (hε : 1+ε ≠ 0) :
    (currentD d ε t u).re = 1-(2+ε^2/(1+ε))*Real.cos d.theta+
      Real.cosh (-d.c₀*ε+d.tau*t/2)*Real.cos (-d.thetaB+u) ∧
    -(currentD d ε t u).im = (2*ε-ε^2/(1+ε))*Real.sin d.theta-
      Real.sinh (-d.c₀*ε+d.tau*t/2)*Real.sin (-d.thetaB+u) := by
  obtain ⟨hr,hi⟩ := radial_trace_components d.theta ε hε
  obtain ⟨hwr,hwi⟩ := plateau_dispersion_components (radialParameter d.theta ε)
    d.c₀ ε d.tau t d.thetaB u
  rw [currentD,currentW_dispersion]
  simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub,
    neg_neg,hwr,hwi,hr,hi]
  exact ⟨by ring,trivial⟩

/-- Complex analytic extension used only to estimate the actual real radial
formula. The next theorem identifies it at every admissible real point. -/
def radialTraceModel (d : LocalBranchData) (e : ℂ) : ℂ :=
  (2+e^2/(1+e))*(Real.cos d.theta:ℂ)+
    Complex.I*(2*e-e^2/(1+e))*(Real.sin d.theta:ℂ)

def branchDModel (d : LocalBranchData) (z : ℂ × ℂ × ℂ) : ℂ :=
  1-radialTraceModel d z.1+
    Complex.cosh (-(d.c₀:ℂ)*z.1+(d.tau:ℂ)*z.2.1/2+
      (-(d.thetaB:ℂ)+z.2.2)*Complex.I)

theorem radialTraceModel_eq (d : LocalBranchData) (ε : ℝ) (hε : 1+ε ≠ 0) :
    radialTraceModel d (ε:ℂ) = radialParameter d.theta ε+(radialParameter d.theta ε)⁻¹ := by
  obtain ⟨hr,hi⟩ := radial_trace_components d.theta ε hε
  have he : radialTraceModel d (ε:ℂ) =
      (((2+ε^2/(1+ε))*Real.cos d.theta:ℝ):ℂ)+
        Complex.I*(((2*ε-ε^2/(1+ε))*Real.sin d.theta:ℝ):ℂ) := by
    unfold radialTraceModel
    push_cast
    ring
  rw [he]
  apply Complex.ext
  · simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero] using hr.symm
  · simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add,add_zero] using hi.symm

theorem branchDModel_eq (d : LocalBranchData) (ε t u : ℝ) (hε : 1+ε ≠ 0) :
    branchDModel d ((ε:ℂ),(t:ℂ),(u:ℂ)) = currentD d ε t u := by
  rw [branchDModel,radialTraceModel_eq d ε hε]
  simp [currentD,currentW,plateauW]
  ring

theorem branchDModel_zero (d : LocalBranchData) : branchDModel d 0 = 0 := by
  have ha : (Real.cos d.thetaB:ℂ) = 2*(Real.cos d.theta:ℂ)-1 := by
    exact_mod_cast d.angle_relation
  simp [branchDModel,radialTraceModel,Complex.cosh_mul_I,← Complex.ofReal_cos,ha]

theorem branchDModel_analytic (d : LocalBranchData) : AnalyticAt ℂ (branchDModel d) 0 := by
  unfold branchDModel radialTraceModel
  fun_prop (disch := norm_num)

end
end IsingBulk.Branch
