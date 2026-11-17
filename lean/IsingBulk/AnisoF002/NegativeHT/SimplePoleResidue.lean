import IsingBulk.AnisoF002.NegativeHT.MovingPole
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The residue of the actual exponential phase kernel

The physical coth(Γ/2) kernel is `(exp Γ+1)/(exp Γ-1)`.  At a resonant
phase value and a nonzero temperature derivative, its punctured complex
residue is exactly `2/Γ'`.  This calculation retains a general continuous
numerator, so it applies to the original density once that numerator is
constructed.  It does not assert the unproved uniform density estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open Filter
open scoped Topology

noncomputable section

def phasePoleKernel (Γ : ℂ → ℂ) (t : ℂ) : ℂ :=
  (Complex.exp (Γ t)+1)/(Complex.exp (Γ t)-1)

/-- The exponential expression is exactly the physical hyperbolic
quotient, including Lean's totalized values at its zeros. -/
theorem phasePoleKernel_eq_cosh_div_sinh (Γ : ℂ → ℂ) (t : ℂ) :
    phasePoleKernel Γ t = Complex.cosh (Γ t/2)/Complex.sinh (Γ t/2) := by
  let E := Complex.exp (Γ t/2)
  have he : E≠0 := Complex.exp_ne_zero _
  have he2 : Complex.exp (Γ t)=E^2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hc : Complex.cosh (Γ t/2)=(E^2+1)/(2*E) := by
    rw [Complex.cosh, Complex.exp_neg]
    change (E+E⁻¹)/2=(E^2+1)/(2*E)
    field_simp
  have hs : Complex.sinh (Γ t/2)=(E^2-1)/(2*E) := by
    rw [Complex.sinh, Complex.exp_neg]
    change (E-E⁻¹)/2=(E^2-1)/(2*E)
    field_simp
  rw [phasePoleKernel, he2, hc, hs,
    div_div_div_cancel_right₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) he)]

/-- Exact resonance at every particle index divisible by the rational
edge denominator. -/
theorem exp_resonant_phase_center (n p : ℕ) (r : ℤ) (hp : 0<p) (hpn : p∣n) :
    Complex.exp ((n:ℂ)*(((2*Real.pi*(r:ℝ)/(p:ℝ):ℝ):ℂ)*Complex.I)) = 1 := by
  obtain ⟨k,rfl⟩ := hpn
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  convert Complex.exp_int_mul_two_pi_mul_I ((k:ℤ)*r) using 1
  congr 1
  push_cast
  field_simp

/-- The residue is obtained from a genuine punctured complex limit of
the kernel, not from a formal rational replacement. -/
theorem phasePoleKernel_residue {Γ : ℂ → ℂ} {t₀ D : ℂ}
    (hΓ : HasDerivAt Γ D t₀) (hres : Complex.exp (Γ t₀)=1) (hD : D≠0) :
    Tendsto (fun t : ℂ => (t-t₀)*phasePoleKernel Γ t)
      (𝓝[≠] t₀) (𝓝 (2/D)) := by
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (Γ t)-1) D t₀ := by
    simpa only [hres, one_mul] using hΓ.cexp.sub_const (1:ℂ)
  have hs : Tendsto (fun t : ℂ => (Complex.exp (Γ t)-1)/(t-t₀))
      (𝓝[≠] t₀) (𝓝 D) := by
    convert hd.tendsto_slope using 1
    funext t
    simp [slope, hres, div_eq_mul_inv, mul_comm]
  have hn : Tendsto (fun t : ℂ => Complex.exp (Γ t)+1)
      (𝓝[≠] t₀) (𝓝 (2:ℂ)) := by
    have hc : ContinuousAt (fun t : ℂ => Complex.exp (Γ t)+1) t₀ :=
      hΓ.continuousAt.cexp.add continuousAt_const
    simpa only [hres, one_add_one_eq_two] using hc.tendsto.mono_left nhdsWithin_le_nhds
  convert hn.mul (hs.inv₀ hD) using 1
  · funext t
    simp only [phasePoleKernel, inv_div]
    ring
  · ring

/-- Exact residue with the full numerator retained symbolically.  The
minus sign in F002's Taylor pole-density comes later from expanding
`(t-T)⁻¹` at the Taylor center, not from this residue computation. -/
theorem weighted_phasePoleKernel_residue {Γ F : ℂ → ℂ} {t₀ D : ℂ}
    (hΓ : HasDerivAt Γ D t₀) (hres : Complex.exp (Γ t₀)=1) (hD : D≠0)
    (hF : ContinuousAt F t₀) :
    Tendsto (fun t : ℂ => (t-t₀)*(F t*phasePoleKernel Γ t))
      (𝓝[≠] t₀) (𝓝 (2*F t₀/D)) := by
  have hp := phasePoleKernel_residue hΓ hres hD
  have hf : Tendsto F (𝓝[≠] t₀) (𝓝 (F t₀)) :=
    hF.tendsto.mono_left nhdsWithin_le_nhds
  convert hf.mul hp using 1
  · funext t
    ring
  · ring

theorem weighted_phasePoleKernel_residue_ne_zero {F₀ D : ℂ}
    (hF : F₀≠0) (hD : D≠0) : 2*F₀/D≠0 :=
  div_ne_zero (mul_ne_zero (by norm_num) hF) hD

end

end IsingBulk.AnisoF002.NegativeHT
