import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds
import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticHadamard
import Mathlib.Analysis.Calculus.Deriv.Add

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

theorem deriv_zero_of_even_complex (f : ℂ → ℂ) (he : ∀ v, f (-v)=f v) : deriv f 0=0 := by
  by_cases hf : DifferentiableAt ℂ f 0
  · have hf' : HasDerivAt f (deriv f 0) (-(0:ℂ)) := by simpa using hf.hasDerivAt
    have hh := hf'.comp 0 (hasDerivAt_id (0:ℂ)).neg
    have hh' : HasDerivAt f (-(deriv f 0)) 0 := by
      simpa only [Function.comp_def,he,mul_neg_one] using hh
    have hd := hh'.unique hf.hasDerivAt
    linear_combination -hd / 2
  · exact deriv_zero_of_not_differentiableAt hf

theorem phaseEnergy_even_at_delta_zero (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (t v : ℂ) :
    phaseEnergy B phi hphi 0 t (-v)=phaseEnergy B phi hphi 0 t v := by
  have hd := deriv_zero_of_even_complex (negativePhase B phi hphi t)
    (negativePhase_even B phi hphi t)
  simp only [phaseEnergy,energyQuotient,energyRemainder,hd,zero_mul,sub_zero,zero_add,
    negativePhase_even,neg_eq_zero,neg_sq]

theorem phaseRootEnergy_deriv_zero (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (t : ℂ) :
    deriv (fun v => Complex.sqrt (phaseEnergy B phi hphi 0 t v)) 0=0 :=
  deriv_zero_of_even_complex _ (fun v => congrArg Complex.sqrt (phaseEnergy_even_at_delta_zero B phi hphi t v))

theorem coordinateHadamard_at_zero_last {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : E × ℂ → ℂ) (x : E) :
    coordinateHadamard f (x,0)=fderiv ℂ f (x,0) (0,1) := by
  simp [coordinateHadamard,coordinateContraction_apply]

end
end IsingBulk.Anisotropic.NegativeNormalForm
