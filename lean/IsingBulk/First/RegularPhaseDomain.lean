import IsingBulk.Analysis.BranchUpper
import IsingBulk.First.MeanRootBridge
import IsingBulk.First.MeanNonlinearBound

/-! Upper-half-plane physical-root and whole lower-strip domain adapters,
plus the curvature-sign-invariant nonlinear gap. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem lowerArccos_analytic_cos_of_lt_pi (beta : ℝ) (hb : 0 < beta)
    (hbpi : beta < Real.pi) : AnalyticAt ℂ lowerArccos (Real.cos beta:ℂ) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  apply IsingBulk.Branch.lowerArccos_analytic_of_slit
  · left
    have hsq := Real.sin_sq_add_cos_sq beta
    simp only [Complex.sub_re,Complex.one_re,← Complex.ofReal_pow,Complex.ofReal_re]
    nlinarith [sq_pos_of_pos hs]
  · right
    have hroot : inverseCosineRoot (Real.cos beta:ℂ) =
        Complex.exp ((beta:ℂ)*Complex.I) := by
      have hsq : (1-(Real.cos beta:ℂ)^2) = ((Real.sin beta)^2:ℝ) := by
        have h := Real.sin_sq_add_cos_sq beta
        push_cast
        exact_mod_cast (show 1-(Real.cos beta)^2 = (Real.sin beta)^2 by linarith)
      rw [inverseCosineRoot, hsq, sqrt_ofReal_nonnegative _ (sq_nonneg _),
        Real.sqrt_sq hs.le, Complex.exp_ofReal_mul_I]
      ring
    rw [hroot,Complex.exp_ofReal_mul_I_im]
    exact hs.ne'


theorem phaseRoot_norm_lt_one_of_upper {W : ℂ} (hW : 0 < W.im) :
    ‖phaseRoot W‖ < 1 := by
  rw [phaseRoot,Complex.norm_exp,Real.exp_lt_one_iff]
  simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg]
    using (lowerArccos_sheet_of_upper hW).2.2.2

theorem phaseRoot_eq_interior_root_of_upper {W z : ℂ}
    (hz : z^2-2*W*z+1=0) (hzn : ‖z‖ < 1) (hi : 0 < W.im) : phaseRoot W = z :=
  quadratic_root_unique (phaseRoot_quadratic W) hz (phaseRoot_norm_lt_one_of_upper hi) hzn

/-- Both variables may lie anywhere on the strict lower angular semicircle,
including the entire quadrant-II source chart. -/
theorem exp_pair_denominator_ne_zero_lower_strip {u v : ℂ}
    (hu : -Real.pi < u.im ∧ u.im < 0) (hv : -Real.pi < v.im ∧ v.im < 0) :
    1-exp u*exp v ≠ 0 := by
  intro hz
  have he : exp (u+v)=1 := by rw [exp_add]; exact (sub_eq_zero.mp hz).symm
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hm
  simp at him
  have hmlo : (-1:ℝ)<m := by nlinarith [Real.pi_pos,hu.1,hv.1]
  have hmhi : (m:ℝ)<0 := by nlinarith [Real.pi_pos,hu.2,hv.2]
  have hlo : (-1:ℤ)<m := by exact_mod_cast hmlo
  have hhi : m<(0:ℤ) := by exact_mod_cast hmhi
  omega

/-- The nonlinear gap is invariant under reversal of the phase-separation
sign. This is the only sign change in the negative-curvature shape gap. -/
theorem nonlinear_exp_gap_signed {w : ℂ} {sigma epsilon q a b C : ℝ}
    (hsigma : sigma=1 ∨ sigma= -1)
    (ha : 0<a) (hb : 0<b) (hC : 0≤C) (he : 0≤epsilon) (he1 : epsilon≤1)
    (hw : ‖w‖≤1/2) (hattenuation : w.re≤ -a*epsilon)
    (hphase : b*q-C*epsilon^2≤sigma*w.im) :
    (a*b/(2*(a+b+C)))*(epsilon+q)≤‖1-exp w‖ := by
  rcases hsigma with rfl | rfl
  · simp only [one_mul] at hphase
    exact nonlinear_exp_gap ha hb hC he he1 hw hattenuation hphase
  · have h := nonlinear_exp_gap (w := star w) ha hb hC he he1
      (by simpa using hw) (by simpa using hattenuation) (by simpa using hphase)
    have hn : ‖1-exp (star w)‖ = ‖1-exp w‖ := by
      simpa only [star_sub,star_one,Complex.star_def,Complex.exp_conj]
        using (norm_star (1-exp w))
    rwa [hn] at h

end
end IsingBulk.First.Regular
