import IsingBulk.Anisotropic.Geometry.ExactSpectralSet
import Mathlib.NumberTheory.Real.Irrational

namespace IsingBulk.Anisotropic
noncomputable section

/-- A period of the entire unsquared spectral set, not of either susceptibility. -/
def ImaginarySpectralPeriod (lam t : ℝ) : Prop :=
  ∀z : ℂ,z+(t:ℂ)*Complex.I∈spectralSet lam ↔ z∈spectralSet lam

theorem cos_sq_add_nat_pi (y : ℝ) (n : ℕ) :
    Real.cos (y+n*Real.pi)^2=Real.cos y^2 := by
  have hp : Function.Periodic (fun x : ℝ=>Real.cos x^2) Real.pi := fun x=>by
    dsimp only
    rw [Real.cos_add_pi,neg_sq]
  exact hp.nat_mul n y

/-- Every positive rational ratio r/s has imaginary spectral period pi*s;
no reduction or parity condition on r,s is necessary. -/
theorem rational_imaginary_spectral_period {lam : ℝ} (hlam : 0<lam)
    (r s : ℕ) (h : lam*(s:ℝ)=r) : ImaginarySpectralPeriod lam (s*Real.pi) := by
  intro z
  rw [mem_spectralSet_iff_signs hlam,mem_spectralSet_iff_signs hlam]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_one,mul_zero,sub_zero,add_zero]
  have hangle : lam*(z.im+s*Real.pi)=lam*z.im+r*Real.pi := by rw [mul_add,←mul_assoc,h]
  simp only [geometryF1,geometryF2,hangle,cos_sq_add_nat_pi]

end
end IsingBulk.Anisotropic
