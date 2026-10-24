import IsingBulk.Anisotropic.Geometry.SpectralAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

def spectralDet (lam : ℝ) (z : ℂ) : ℝ :=
  (spectralS z).re * (spectralT lam z).im - (spectralS z).im * (spectralT lam z).re

def spectralNU (lam : ℝ) (z : ℂ) : ℝ :=
  (spectralA lam z).re * (spectralT lam z).im - (spectralA lam z).im * (spectralT lam z).re

def spectralNV (lam : ℝ) (z : ℂ) : ℝ :=
  (spectralS z).re * (spectralA lam z).im - (spectralS z).im * (spectralA lam z).re

def spectralU (lam : ℝ) (z : ℂ) : ℝ := spectralNU lam z / spectralDet lam z
def spectralV (lam : ℝ) (z : ℂ) : ℝ := spectralNV lam z / spectralDet lam z

theorem cramer_reconstruction (a b A : ℂ) (hd : a.re*b.im - a.im*b.re ≠ 0) :
    A = a * (((A.re*b.im-A.im*b.re)/(a.re*b.im-a.im*b.re) : ℝ) : ℂ) +
      b * (((a.re*A.im-a.im*A.re)/(a.re*b.im-a.im*b.re) : ℝ) : ℂ) := by
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  all_goals rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, eq_div_iff hd]
  all_goals ring

theorem spectral_reconstruction {lam : ℝ} {z : ℂ} (hd : spectralDet lam z ≠ 0) :
    spectralA lam z = spectralS z * (spectralU lam z : ℂ) + spectralT lam z * (spectralV lam z : ℂ) :=
  cramer_reconstruction _ _ _ hd

/-- Exact unsquared membership criterion away from collinearity. -/
theorem mem_spectralSet_iff_coordinates {lam : ℝ} {z : ℂ} (hd : spectralDet lam z ≠ 0) :
    z ∈ spectralSet lam ↔ |spectralU lam z| ≤ 1 ∧ |spectralV lam z| ≤ 1 := by
  constructor
  · rintro ⟨u,hu,v,hv,h⟩
    have he := real_coordinates_injective _ _ hd u v (spectralU lam z) (spectralV lam z)
      (h.symm.trans (spectral_reconstruction hd))
    rw [← he.1, ← he.2]
    exact ⟨abs_le.mpr hu, abs_le.mpr hv⟩
  · rintro ⟨hu,hv⟩
    exact ⟨spectralU lam z, abs_le.mp hu, spectralV lam z, abs_le.mp hv, spectral_reconstruction hd⟩

/-- The exact factorization (2.6) is polynomial and does not divide by D. -/
theorem numeratorU_factor (h c H C t q T Q : ℝ) :
    (c*t*T*Q-h*H*C*q)^2 - (h*C*t*Q-c*H*q*T)^2 =
      (c^2*T^2-h^2*C^2)*(t^2*Q^2-H^2*q^2) := by ring

/-- The exact factorization (2.7) likewise retains collinear configurations. -/
theorem numeratorV_factor (h c H C t q T Q : ℝ) :
    (h*c*H*Q-C*t*q*T)^2 - (h*C*t*Q-c*H*q*T)^2 =
      (c^2*H^2-C^2*t^2)*(h^2*Q^2-q^2*T^2) := by ring

end
end IsingBulk.Anisotropic
