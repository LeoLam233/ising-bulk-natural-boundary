import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy
import Mathlib.Analysis.Complex.SqrtDeriv

/-! The actual central separable quotient and its tangent-normalized square-root
map. This does not replace the parameter-dependent, dimension-uniform pole map. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

def centralParameterSlope (B : ℂ → ℂ) (phi : ℝ) (d : ℂ) : ℂ :=
  ((Real.sin phi : ℂ) * Complex.I)⁻¹ * B (1 - Complex.cos d)

def centralEnergy (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d v : ℂ) : ℂ :=
  let g := negativePhase B phi hphi (1 - Complex.cos d)
  energyQuotient g (deriv g d) d (centralHessian B phi d) (centralParameterSlope B phi d) v

theorem centralParameterSlope_ne_zero (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : B (1 - Complex.cos d) ≠ 0) :
    centralParameterSlope B phi d ≠ 0 :=
  mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) hB

theorem centralEnergy_zero (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hh : centralHessian B phi d ≠ 0) (hB : B (1 - Complex.cos d) ≠ 0) :
    centralEnergy B phi hphi d 0 = 1 := by
  have ha := centralParameterSlope_ne_zero B phi hphi d hB
  have hd := (negativePhase_second_delta_hessian B phi hphi d).deriv
  simp only [centralEnergy, energyQuotient, ↓reduceIte, hd, neg_mul, neg_neg]
  exact div_self (mul_ne_zero hh ha)

theorem negativePhase_analyticAt_delta_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    AnalyticAt ℂ (negativePhase B phi hphi (1 - Complex.cos d)) d := by
  have hw : AnalyticAt ℂ (negativeDispersion B (Real.cos phi) (1 - Complex.cos d)) d :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_const.add Complex.analyticAt_cos))
  exact (edgePhase_spec phi hphi).1.comp_of_eq hw (negativeDispersion_center B (Real.cos phi) d)

theorem centralEnergy_analyticAt_zero (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    AnalyticAt ℂ (centralEnergy B phi hphi d) 0 :=
  energyQuotient_analyticAt_zero (negativePhase_analyticAt_delta_center B phi hphi d)

/-- The actual square-root energy coordinate is tangent to the identity.
No statement about the complex nullcone or an assumed normal form is used. -/
theorem centralSeparableMap_hasDerivAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hh : centralHessian B phi d ≠ 0) (hB : B (1 - Complex.cos d) ≠ 0) :
    HasDerivAt (fun v : ℂ => v * Complex.sqrt (centralEnergy B phi hphi d v)) 1 0 := by
  have hE := centralEnergy_analyticAt_zero B phi hphi d
  have h0 := centralEnergy_zero B phi hphi d hh hB
  have hs : centralEnergy B phi hphi d 0 ∈ Complex.slitPlane := by
    rw [h0]
    exact Complex.one_mem_slitPlane
  have hd := (Complex.hasDerivAt_sqrt hs).comp 0 hE.differentiableAt.hasDerivAt
  simpa only [Pi.mul_def, Function.comp_def, id_eq, h0, Complex.sqrt_one, mul_one, one_mul, zero_mul, add_zero]
    using (hasDerivAt_id (0 : ℂ)).mul hd

end
end IsingBulk.Anisotropic.NegativeNormalForm
