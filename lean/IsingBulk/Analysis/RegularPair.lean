import IsingBulk.Analysis.RegularCoordinates
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Exact cancellation in eq:branchregular. The quotient functions below are
defined through their removable values. The pointwise rational expression is
compared only away from its denominator zeros. -/
namespace IsingBulk.Branch
noncomputable section

def halfSineQuotient : ℂ → ℂ := dslope (fun z : ℂ => Complex.sin (z/2)) 0
def exponentialQuotient : ℂ → ℂ := dslope (fun z : ℂ => 1-Complex.exp (-Complex.I*z)) 0

theorem mul_halfSineQuotient (z : ℂ) : z*halfSineQuotient z = Complex.sin (z/2) := by
  simpa [halfSineQuotient, smul_eq_mul] using
    sub_smul_dslope (fun z : ℂ => Complex.sin (z/2)) 0 z

theorem mul_exponentialQuotient (z : ℂ) :
    z*exponentialQuotient z = 1-Complex.exp (-Complex.I*z) := by
  simpa [exponentialQuotient, smul_eq_mul] using
    sub_smul_dslope (fun z : ℂ => 1-Complex.exp (-Complex.I*z)) 0 z

theorem halfSineQuotient_analytic : AnalyticAt ℂ halfSineQuotient 0 := by
  have h : AnalyticAt ℂ (fun z : ℂ => Complex.sin (z/2)) 0 := by fun_prop
  obtain ⟨p, hp⟩ := h
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem exponentialQuotient_analytic : AnalyticAt ℂ exponentialQuotient 0 := by
  have h : AnalyticAt ℂ (fun z : ℂ => 1-Complex.exp (-Complex.I*z)) 0 := by fun_prop
  obtain ⟨p, hp⟩ := h
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem halfSineQuotient_zero : halfSineQuotient 0 = 1/2 := by
  rw [halfSineQuotient, dslope_same]
  have h := ((hasDerivAt_id (0:ℂ)).div_const 2).csin
  simpa only [id_eq, zero_div, Complex.cos_zero, one_mul] using h.deriv

theorem exponentialQuotient_zero : exponentialQuotient 0 = Complex.I := by
  rw [exponentialQuotient, dslope_same]
  have h := (((hasDerivAt_id (0:ℂ)).const_mul (-Complex.I)).cexp).const_sub 1
  simpa using h.deriv

def regularDifferenceCoefficient (s p q : ℂ) : ℂ :=
  4*halfSineQuotient (p+q)*halfSineQuotient (p-q)/
    (1-(regularY s p*regularY s q)⁻¹)

theorem regularY_difference (s p q : ℂ)
    (hd : 1-(regularY s p*regularY s q)⁻¹ ≠ 0) :
    regularY s p-regularY s q = (p-q)*(p+q)*regularDifferenceCoefficient s p q := by
  have hp := dispersion_regularY s p
  have hq := dispersion_regularY s q
  unfold dispersion at hp hq
  have ht : regularY s p+(regularY s p)⁻¹-(regularY s q+(regularY s q)⁻¹) =
      -2*(Complex.cos p-Complex.cos q) := by linear_combination -2*hp+2*hq
  have halg : (regularY s p-regularY s q)*(1-(regularY s p*regularY s q)⁻¹) =
      regularY s p+(regularY s p)⁻¹-(regularY s q+(regularY s q)⁻¹) := by
    field_simp [regularY_ne_zero]
    ring
  rw [ht, Complex.cos_sub_cos] at halg
  apply (mul_left_inj' hd).mp
  rw [halg]
  unfold regularDifferenceCoefficient
  conv_rhs => rw [mul_assoc, div_mul_cancel₀ _ hd]
  rw [← mul_halfSineQuotient (p+q), ← mul_halfSineQuotient (p-q)]
  ring

def regularPairCoefficient (s p q : ℂ) : ℂ :=
  -(regularDifferenceCoefficient s p q)^2 * Complex.exp (-Complex.I*p) *
    Complex.exp (-Complex.I*q) /
    (regularY s p*regularY s q*(exponentialQuotient (p+q))^2)

theorem regular_pair_cancellation (s p q : ℂ)
    (hd : 1-(regularY s p*regularY s q)⁻¹ ≠ 0)
    (hsum : p+q ≠ 0) (hJ : exponentialQuotient (p+q) ≠ 0) :
    -(regularY s p-regularY s q)^2 * Complex.exp (-Complex.I*p) *
      Complex.exp (-Complex.I*q) /
      (regularY s p*regularY s q*
        (1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q))^2) =
      (p-q)^2*regularPairCoefficient s p q := by
  have he : 1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q) =
      (p+q)*exponentialQuotient (p+q) := by
    rw [mul_exponentialQuotient, ← Complex.exp_add]
    congr 2
    ring
  rw [regularY_difference s p q hd, he]
  unfold regularPairCoefficient
  field_simp

/-- Analyticity of the canceled pair at the full collision, from the actual
inverse dispersion formula. No division by p-q remains in this coefficient. -/
theorem regularPairCoefficient_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularPairCoefficient s z.1 z.2) (0,0) := by
  have hy : AnalyticAt ℂ (regularY s) 0 :=
    AnalyticAt.comp (f := fun φ : ℂ => (s,φ))
      (regularY_analytic_base s c hs hS hc) (analyticAt_const.prod analyticAt_id)
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ => regularY s z.1) (0,0) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := regularY s)
      (x := (0,0)) hy analyticAt_fst
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ => regularY s z.2) (0,0) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.2) (g := regularY s)
      (x := (0,0)) hy analyticAt_snd
  have hsum : AnalyticAt ℂ (fun z : ℂ × ℂ => z.1+z.2) (0,0) :=
    analyticAt_fst.add analyticAt_snd
  have hdiff : AnalyticAt ℂ (fun z : ℂ × ℂ => z.1-z.2) (0,0) :=
    analyticAt_fst.sub analyticAt_snd
  have hsp : AnalyticAt ℂ (fun z : ℂ × ℂ => halfSineQuotient (z.1+z.2)) (0,0) :=
    AnalyticAt.comp_of_eq halfSineQuotient_analytic hsum (by simp)
  have hsm : AnalyticAt ℂ (fun z : ℂ × ℂ => halfSineQuotient (z.1-z.2)) (0,0) :=
    AnalyticAt.comp_of_eq halfSineQuotient_analytic hdiff (by simp)
  have hJ : AnalyticAt ℂ (fun z : ℂ × ℂ => exponentialQuotient (z.1+z.2)) (0,0) :=
    AnalyticAt.comp_of_eq exponentialQuotient_analytic hsum (by simp)
  have hden : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      1-(regularY s z.1*regularY s z.2)⁻¹) (0,0) :=
    analyticAt_const.sub ((hp.mul hq).inv (mul_ne_zero (regularY_ne_zero _ _) (regularY_ne_zero _ _)))
  have hH : AnalyticAt ℂ (fun z : ℂ × ℂ => regularDifferenceCoefficient s z.1 z.2) (0,0) :=
    ((analyticAt_const.mul hsp).mul hsm).div hden (regularY_base_denominator s c hS hc)
  have hep : AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.exp (-Complex.I*z.1)) (0,0) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => -Complex.I*z.1) (g := Complex.exp)
      analyticAt_cexp (analyticAt_const.mul analyticAt_fst)
  have heq : AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.exp (-Complex.I*z.2)) (0,0) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => -Complex.I*z.2) (g := Complex.exp)
      analyticAt_cexp (analyticAt_const.mul analyticAt_snd)
  exact (((hH.pow 2).neg.mul hep).mul heq).div ((hp.mul hq).mul (hJ.pow 2))
    (by simp [exponentialQuotient_zero, regularY_ne_zero])

end
end IsingBulk.Branch

