import IsingBulk.First.ComplementDamping
import IsingBulk.First.ComplementIBP

/-! The actual angular phase to which the complement integration-by-parts
operator applies, including its genuine finite-direction derivative. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators ContDiff

theorem source_complexOfReal_contDiff : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) :=
  Complex.ofRealCLM.contDiff

attribute [local fun_prop] source_complexOfReal_contDiff

/-- Rotate an actual unit-torus configuration by real angular coordinates. -/
def torusShift {N : ℕ} (x : Fin N → ℂ) (u : Fin N → ℝ) : Fin N → ℂ :=
  fun i => angularCurve (x i) (u i) 1

def sourceAngularExponent {N : ℕ} (r : ℝ) (s : ℂ) (x y : Fin N → ℂ)
    (f : SingularFactorIndex N) (u : DoubleAngularVector N) : ℂ :=
  singularFactorExponent r s x y u f 1

theorem angularCurve_shift (r : ℝ) (z : ℂ) (u t e : ℝ) :
    angularCurve ((r : ℂ) * z) (u + t*e) 1 =
      angularCurve ((r : ℂ) * angularCurve z u 1) e t := by
  unfold angularCurve
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_add, Complex.ofReal_mul]
  rw [show ((u : ℂ) + (t : ℂ) * (e : ℂ)) * Complex.I =
      (u : ℂ) * Complex.I + (t : ℂ) * (e : ℂ) * Complex.I by ring, Complex.exp_add]
  ring

theorem sourceAngularExponent_along_direction {N : ℕ} (r : ℝ) (s : ℂ)
    (x y : Fin N → ℂ) (f : SingularFactorIndex N)
    (u e : DoubleAngularVector N) (t : ℝ) :
    sourceAngularExponent r s x y f (u + t • e) =
      singularFactorExponent r s (torusShift x u.1) (torusShift y u.2) e f t := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> simp [sourceAngularExponent, singularFactorExponent, torusShift,
      angularCurve_shift, smul_eq_mul]
  · cases b <;> simp [sourceAngularExponent, singularFactorExponent, torusShift,
      angularCurve_shift, smul_eq_mul]
  · simp [sourceAngularExponent, singularFactorExponent, torusShift, angularCurve_shift, smul_eq_mul]

/-- Each actual active-factor phase is smooth on the complete real angular
space at every nonzero fixed radius. -/
theorem sourceAngularExponent_contDiff {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (f : SingularFactorIndex N) : ContDiff ℝ ∞ (sourceAngularExponent r s x y f) := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hcx (z : Fin N → ℂ) (i : Fin N) :
      ContDiff ℝ ∞ (fun u : DoubleAngularVector N => angularCurve ((r : ℂ)*z i) (u.1 i) 1) := by
    unfold angularCurve
    fun_prop
  have hcy (z : Fin N → ℂ) (i : Fin N) :
      ContDiff ℝ ∞ (fun u : DoubleAngularVector N => angularCurve ((r : ℂ)*z i) (u.2 i) 1) := by
    unfold angularCurve
    fun_prop
  have hn (z : Fin N → ℂ) (hz : ∀ i, z i ≠ 0) (i : Fin N) (a : ℝ) :
      angularCurve ((r : ℂ)*z i) a 1 ≠ 0 := by
    unfold angularCurve
    exact mul_ne_zero (mul_ne_zero hrc (hz i)) (Complex.exp_ne_zero _)
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> unfold sourceAngularExponent singularFactorExponent angularCurve <;> fun_prop
  · cases b <;> unfold sourceAngularExponent singularFactorExponent angularCurve <;> fun_prop
  · have hxC := hcx x i
    have hyC := hcy y i
    have hxI := hxC.inv (fun u => hn x hx i (u.1 i))
    have hyI := hyC.inv (fun u => hn y hy i (u.2 i))
    exact contDiff_const.mul ((contDiff_const.sub ((hxC.add hxI).div_const (2 : ℂ))).sub
      ((hyC.add hyI).div_const (2 : ℂ)))

/-- The imaginary part of the actual Fréchet phase derivative is exactly the
damped source-vector pairing at the rotated torus point. -/
theorem sourceAngularExponent_direction_im {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (f : SingularFactorIndex N) (u e : DoubleAngularVector N) :
    (phaseDirection e (sourceAngularExponent r s x y f) u).im =
      angularDot e (dampedSingularVector r (torusShift x u.1) (torusShift y u.2) f) := by
  have hx0 (i) : x i ≠ 0 := by intro h; have hh := hx i; simp [h] at hh
  have hy0 (i) : y i ≠ 0 := by intro h; have hh := hy i; simp [h] at hh
  have hg := sourceAngularExponent_contDiff r hr s x y hx0 hy0 f
  have hc : HasDerivAt (fun t : ℝ => u + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add u
  have hgd : HasFDerivAt (sourceAngularExponent r s x y f)
      (fderiv ℝ (sourceAngularExponent r s x y f) u) (u + (0 : ℝ) • e) := by
    simpa using (hg.differentiable (by simp) u).hasFDerivAt
  have hd := hgd.comp_hasDerivAt 0 hc
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have heq : (fun t : ℝ => (sourceAngularExponent r s x y f (u + t • e)).im) =
      fun t => (singularFactorExponent r s (torusShift x u.1) (torusShift y u.2) e f t).im := by
    funext t
    rw [sourceAngularExponent_along_direction]
  change HasDerivAt (fun t : ℝ => (sourceAngularExponent r s x y f (u + t • e)).im)
    (phaseDirection e (sourceAngularExponent r s x y f) u).im 0 at hi
  rw [heq] at hi
  have hshiftx (i) : ‖torusShift x u.1 i‖ = 1 := by rw [torusShift, norm_angularCurve, hx i]
  have hshifty (i) : ‖torusShift y u.2 i‖ = 1 := by rw [torusShift, norm_angularCurve, hy i]
  exact hi.unique (singularFactorExponent_im_hasDerivAt r hr s
    (torusShift x u.1) (torusShift y u.2) hshiftx hshifty e f)

end
end IsingBulk.First
