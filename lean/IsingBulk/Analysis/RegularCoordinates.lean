import IsingBulk.Analysis.BranchSheet
import Mathlib.Analysis.Complex.CauchyIntegral

/-! An explicit analytic inverse for the regular branch coordinate.
This proves the inverse dispersion relation and evenness; it does not yet prove
the canceled pair coefficient or the pullback of a top form. -/
namespace IsingBulk.Branch
noncomputable section

def regularY (s φ : ℂ) : ℂ := (inverseCosineRoot (s+s⁻¹-Complex.cos φ))⁻¹

theorem regularY_ne_zero (s φ : ℂ) : regularY s φ ≠ 0 :=
  inv_ne_zero (inverseCosineRoot_ne_zero _)

theorem regularY_even (s φ : ℂ) : regularY s (-φ) = regularY s φ := by
  simp [regularY, Complex.cos_neg]

theorem dispersion_regularY (s φ : ℂ) : dispersion s (regularY s φ) = Complex.cos φ := by
  unfold dispersion regularY
  rw [inv_inv, add_comm ((inverseCosineRoot _)⁻¹), inverseCosineRoot_trace]
  ring

theorem regularY_formula (s φ : ℂ) : regularY s φ =
    (s+s⁻¹-Complex.cos φ)-Complex.I*Complex.sqrt (1-(s+s⁻¹-Complex.cos φ)^2) :=
  inverseCosineRoot_inverse _

/-- A local two-variable analytic inverse follows directly from the chosen
square-root formula. Only a local slit-plane condition is needed. -/
theorem regularY_analytic (s φ : ℂ) (hs : s ≠ 0)
    (hslit : 1-(s+s⁻¹-Complex.cos φ)^2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularY z.1 z.2) (s,φ) := by
  have hH : AnalyticAt ℂ (fun z : ℂ × ℂ => z.1+z.1⁻¹-Complex.cos z.2) (s,φ) :=
    (analyticAt_fst.add (analyticAt_fst.inv hs)).sub
      (Complex.analyticAt_cos.comp analyticAt_snd)
  have hP : AnalyticAt ℂ (fun z : ℂ × ℂ => 1-(z.1+z.1⁻¹-Complex.cos z.2)^2) (s,φ) :=
    analyticAt_const.sub (hH.pow 2)
  have hS : AnalyticAt ℂ Complex.sqrt (1-(s+s⁻¹-Complex.cos φ)^2) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hR : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      z.1+z.1⁻¹-Complex.cos z.2 - Complex.I*Complex.sqrt
        (1-(z.1+z.1⁻¹-Complex.cos z.2)^2)) (s,φ) :=
    hH.sub (analyticAt_const.mul (AnalyticAt.comp
      (f := fun z : ℂ × ℂ => 1-(z.1+z.1⁻¹-Complex.cos z.2)^2)
      (g := Complex.sqrt) hS hP))
  exact hR.congr (Filter.Eventually.of_forall (fun z => (regularY_formula z.1 z.2).symm))

/-- The source base point lies strictly inside this local analytic chart. -/
theorem regularY_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularY z.1 z.2) (s,0) := by
  apply regularY_analytic s 0 hs
  apply Or.inl
  simp only [Complex.cos_zero, hS, add_sub_cancel_left, ← Complex.ofReal_pow,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hc' := abs_lt.mp hc
  nlinarith

/-- Exact cancellation of the selected difference via a divided difference.
Joint analyticity and uniform jets of this quotient remain to be supplied. -/
theorem selected_difference_factorization (B : ℂ → ℂ) (p q : ℂ) :
    B p*q-B q*p = (q-p)*(B p-p*dslope B p q) := by
  have h := sub_smul_dslope B p q
  simp only [smul_eq_mul] at h
  linear_combination p*h

theorem regularY_base_denominator (s : ℂ) (c : ℝ)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    1-(regularY s 0*regularY s 0)⁻¹ ≠ 0 := by
  intro h
  have hinv : (regularY s 0*regularY s 0)⁻¹ = 1 := (sub_eq_zero.mp h).symm
  have hsq : regularY s 0*regularY s 0 = 1 := inv_eq_one.mp hinv
  have hyinv : (regularY s 0)⁻¹ = regularY s 0 := inv_eq_of_mul_eq_one_right hsq
  have hdisp := dispersion_regularY s 0
  simp only [dispersion, hS, Complex.cos_zero, hyinv] at hdisp
  have hy : regularY s 0 = (c:ℂ) := by linear_combination -hdisp
  rw [hy] at hsq
  have hreal : c*c = 1 := by exact_mod_cast hsq
  have habs := abs_lt.mp hc
  nlinarith

theorem sqrt_ofReal_nonnegative (x : ℝ) (hx : 0 ≤ x) :
    Complex.sqrt (x:ℂ) = (Real.sqrt x:ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, add_self_div_two]

/-- At φ=0 the inverse is precisely the lower root, with the source angle. -/
theorem regularY_base_selected (s : ℂ) (c : ℝ)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    regularY s 0 = Complex.exp (-((Real.arccos c:ℝ):ℂ)*Complex.I) := by
  have hc' := abs_lt.mp hc
  have hpos : 0 ≤ 1-c^2 := by nlinarith
  rw [regularY_formula]
  simp only [Complex.cos_zero, hS, add_sub_cancel_left]
  rw [show (1-(c:ℂ)^2) = ((1-c^2:ℝ):ℂ) by push_cast; rfl,
    sqrt_ofReal_nonnegative _ hpos]
  rw [show -((Real.arccos c:ℝ):ℂ)*Complex.I =
      ((-Real.arccos c:ℝ):ℂ)*Complex.I by simp,
    Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Real.cos_arccos hc'.1.le hc'.2.le,
    Real.sin_arccos, Complex.ofReal_neg]
  ring

end
end IsingBulk.Branch
