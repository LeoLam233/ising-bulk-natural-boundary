import IsingBulk.Analysis.BranchSheet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact radial-center and plateau formulas needed before the uniform branch
estimates. No global disk or selector theorem is assumed. -/
namespace IsingBulk.Branch
noncomputable section

def radialParameter (θ ε : ℝ) : ℂ := ((1+ε:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)

theorem radial_trace_components (θ ε : ℝ) (hε : 1+ε ≠ 0) :
    (radialParameter θ ε+(radialParameter θ ε)⁻¹).re =
      (2+ε^2/(1+ε))*Real.cos θ ∧
    (radialParameter θ ε+(radialParameter θ ε)⁻¹).im =
      (2*ε-ε^2/(1+ε))*Real.sin θ := by
  have hneg : (Complex.exp ((θ:ℂ)*Complex.I))⁻¹ =
      Complex.exp (-((θ:ℂ)*Complex.I)) := (Complex.exp_neg _).symm
  have hnorm : Complex.normSq (1+(ε:ℂ)) = (1+ε)^2 := by
    simp [Complex.normSq_apply]
    ring
  simp only [radialParameter, mul_inv_rev, hneg, ← Complex.ofReal_inv]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  simp only [hnorm]
  constructor <;> field_simp <;> ring

def plateauW (s : ℂ) (v θB : ℝ) (u : ℂ) : ℂ :=
  s+s⁻¹-Complex.cosh ((v:ℂ)+(-(θB:ℂ)+u)*Complex.I)

theorem plateauW_eq_dispersion (s : ℂ) (c₀ ε τ t θB u : ℝ) :
    plateauW s (-c₀*ε+τ*t/2) θB (u:ℂ) =
      dispersion s (plateauY c₀ ε τ t θB u) := by
  rw [plateauY, polar_dispersion]
  simp [plateauW]

theorem plateauW_hasDerivAt (s : ℂ) (v θB : ℝ) (u : ℂ) :
    HasDerivAt (plateauW s v θB)
      (-Complex.sinh ((v:ℂ)+(-(θB:ℂ)+u)*Complex.I)*Complex.I) u := by
  have hin : HasDerivAt (fun z : ℂ => (v:ℂ)+(-(θB:ℂ)+z)*Complex.I) Complex.I u := by
    convert (((hasDerivAt_id u).const_add (-(θB:ℂ))).mul_const Complex.I).const_add (v:ℂ)
      using 1 <;> simp
  have hout := (Complex.hasDerivAt_cosh ((v:ℂ)+(-(θB:ℂ)+u)*Complex.I)).comp u hin
  convert! hout.const_sub (s+s⁻¹) using 1
  simp [neg_mul]

theorem plateau_phase_hasDerivAt (s : ℂ) (v θB u : ℝ)
    (hre : 0 < (plateauW s v θB (u:ℂ)).re)
    (him : 0 < (plateauW s v θB (u:ℂ)).im) :
    HasDerivAt (fun x : ℝ => lowerArccos (plateauW s v θB (x:ℂ)))
      ((-1/Complex.sin (lowerArccos (plateauW s v θB (u:ℂ)))) *
      (-Complex.sinh ((v:ℂ)+(-(θB:ℂ)+(u:ℂ))*Complex.I)*Complex.I)) u := by
  have ho := (lowerArccos_differentiable _ hre him).hasDerivAt
  rw [lowerArccos_deriv _ hre him] at ho
  exact (ho.comp (u:ℂ) (plateauW_hasDerivAt s v θB (u:ℂ))).comp_ofReal

end
end IsingBulk.Branch
