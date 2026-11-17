import IsingBulk.AnisoF002.C03.IsotropicParameterHolomorphy

/-!
# Actual radial derivatives in the complete constrained current

The radial path is the original exterior physical path. Its scalar
derivative is nonzero and bounded on every positive radial interval.
For a parameter-holomorphic density the real radial derivative is the
same scalar factor times the full parameter component of the current.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology

def isotropicRadialDerivative (α ε : ℝ) : ℂ :=
  Complex.exp ((α : ℂ) * Complex.I) -
    Complex.exp ((α : ℂ) * Complex.I) / isotropicExteriorRadial α ε ^ 2

theorem isotropicExteriorRadial_hasDerivAt (α ε : ℝ) :
    HasDerivAt (isotropicExteriorRadial α)
      (Complex.exp ((α : ℂ) * Complex.I)) ε := by
  change HasDerivAt (fun u : ℝ => ((1 + u : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) _ ε
  simpa [isotropicExteriorRadial] using
    (((hasDerivAt_id ε).const_add 1).ofReal_comp.mul_const
      (Complex.exp ((α : ℂ) * Complex.I)))

theorem isotropicRadialParameter_hasDerivAt (α ε : ℝ) (hε : 0 < ε) :
    HasDerivAt (isotropicRadialParameter α) (isotropicRadialDerivative α ε) ε := by
  change HasDerivAt (fun u => isotropicExteriorRadial α u + (isotropicExteriorRadial α u)⁻¹) _ ε
  have hz : isotropicExteriorRadial α ε ≠ 0 :=
    norm_pos_iff.mp (zero_lt_one.trans (isotropicExteriorRadial_exterior α ε hε))
  convert! (isotropicExteriorRadial_hasDerivAt α ε).add
    ((isotropicExteriorRadial_hasDerivAt α ε).inv hz) using 1
  simp [isotropicRadialDerivative, sub_eq_add_neg, neg_div]

theorem isotropicRadialDerivative_norm_le (α ε : ℝ) (hε : 0 < ε) :
    ‖isotropicRadialDerivative α ε‖ ≤ 2 := by
  have hz := isotropicExteriorRadial_exterior α ε hε
  have hq : ‖Complex.exp ((α : ℂ) * Complex.I) / isotropicExteriorRadial α ε ^ 2‖ < 1 := by
    rw [norm_div, Complex.norm_exp_ofReal_mul_I, norm_pow]
    exact (div_lt_one (by positivity)).mpr (by nlinarith)
  exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp_ofReal_mul_I]; linarith)

theorem isotropicRadialDerivative_ne_zero (α ε : ℝ) (hε : 0 < ε) :
    isotropicRadialDerivative α ε ≠ 0 := by
  intro hz
  have he := sub_eq_zero.mp hz
  have hh := congrArg norm he
  rw [Complex.norm_exp_ofReal_mul_I, norm_div, Complex.norm_exp_ofReal_mul_I, norm_pow] at hh
  have hn := isotropicExteriorRadial_exterior α ε hε
  have hlt : 1 / ‖isotropicExteriorRadial α ε‖ ^ 2 < 1 :=
    (div_lt_one (by positivity)).mpr (by nlinarith)
  linarith

theorem isotropicRadialParameter_continuousOn (α : ℝ) :
    ContinuousOn (isotropicRadialParameter α) (Ioi 0) :=
  fun ε hε => (isotropicRadialParameter_hasDerivAt α ε hε).continuousAt.continuousWithinAt

theorem isotropicRadialDerivative_continuousOn (α : ℝ) :
    ContinuousOn (isotropicRadialDerivative α) (Ioi 0) := by
  intro ε hε
  have hz : isotropicExteriorRadial α ε ^ 2 ≠ 0 := pow_ne_zero _
    (norm_pos_iff.mp (zero_lt_one.trans (isotropicExteriorRadial_exterior α ε hε)))
  exact (continuousAt_const.sub (continuousAt_const.div
    ((isotropicExteriorRadial_hasDerivAt α ε).continuousAt.pow 2) hz)).continuousWithinAt

theorem radial_hasDerivAt_scalarPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ × E → ℂ) (θ : E) (p : ℝ → ℂ) (t : ℝ) (p' : ℂ)
    (hp : HasDerivAt p p' t)
    (hf : DifferentiableAt ℝ f (p t, θ))
    (ha : DifferentiableAt ℂ (fun s => f (s, θ)) (p t)) :
    HasDerivAt (fun u => f (p u, θ))
      (p' * scalarPartial f (1, 0) (p t, θ)) t := by
  rw [scalarPartial_parameter_eq_complex_deriv f (p t) θ hf ha]
  simpa only [Function.comp_def, smul_eq_mul] using ha.hasDerivAt.scomp t hp

end
end IsingBulk.AnisoF002.Isotropic
