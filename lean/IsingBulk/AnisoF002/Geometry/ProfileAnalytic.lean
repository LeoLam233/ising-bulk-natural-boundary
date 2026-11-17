import IsingBulk.AnisoF002.Geometry.HighProfiles
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Global analyticity of the actual signed endpoint profiles

F002 eq:signed-profiles and lemma 2.3 (lem:profile-discrete).
The inverses are the existing total Function.invFun profiles.  Their
analyticity follows from the proved two-sided inverse equations and the
strictly positive derivatives of the actual hyperbolic functions.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open Filter Set
open scoped Topology

theorem profileP_analyticAt (lam x : ℝ) : AnalyticAt ℝ (profilePF002 lam) x := by
  have hlin : AnalyticAt ℝ (fun y : ℝ => lam * y) x := analyticAt_const.mul analyticAt_id
  have hs := (Real.analyticAt_sinh (x := lam * x)).comp hlin
  have hc := (Real.analyticAt_cosh (x := lam * x)).comp hlin
  have hh := Real.analyticAt_cosh.mul (hs.div hc (ne_of_gt (Real.cosh_pos _)))
  change AnalyticAt ℝ (fun y => Real.cosh y * Real.tanh (lam * y)) x
  simp only [Real.tanh_eq_sinh_div_cosh]
  exact hh

theorem profileQ_analyticAt (lam x : ℝ) : AnalyticAt ℝ (profileQF002 lam) x := by
  have hlin : AnalyticAt ℝ (fun y : ℝ => lam * y) x := analyticAt_const.mul analyticAt_id
  have hc := (Real.analyticAt_cosh (x := lam * x)).comp hlin
  have ht := Real.analyticAt_sinh.div Real.analyticAt_cosh (ne_of_gt (Real.cosh_pos x))
  change AnalyticAt ℝ (fun y => Real.cosh (lam * y) * Real.tanh y) x
  simp only [Real.tanh_eq_sinh_div_cosh]
  exact hc.mul ht

def profileQDerivativeF002 (lam x : ℝ) : ℝ :=
  lam * profilePDerivativeF002 lam⁻¹ (lam * x)

theorem profileQ_hasDerivAt {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    HasDerivAt (profileQF002 lam) (profileQDerivativeF002 lam x) x := by
  have hh := (profileP_hasDerivAt lam⁻¹ (lam * x)).comp x (hasDerivAt_const_mul lam)
  convert hh using 1
  · funext y
    exact profileQ_eq_axis_exchange hlam y
  · simp only [profileQDerivativeF002, mul_comm]

theorem profileQDerivative_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    0 < profileQDerivativeF002 lam x :=
  mul_pos hlam (profilePDerivative_pos (inv_pos.mpr hlam) _)

theorem profilePInv_analyticAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    AnalyticAt ℝ (profilePInvF002 lam) y := by
  have hf := profileP_analyticAt lam (profilePInvF002 lam y)
  have hd : deriv (profilePF002 lam) (profilePInvF002 lam y) ≠ 0 := by
    rw [(profileP_hasDerivAt lam _).deriv]
    exact ne_of_gt (profilePDerivative_pos hlam _)
  have hcomp : AnalyticAt ℝ (profilePInvF002 lam ∘ profilePF002 lam)
      (profilePInvF002 lam y) := by
    have heq : profilePInvF002 lam ∘ profilePF002 lam = id :=
      funext (profileP_leftInverse hlam)
    rw [heq]
    exact analyticAt_id
  have hi := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hcomp
  rwa [profileP_rightInverse hlam y] at hi

theorem profileQInv_analyticAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    AnalyticAt ℝ (profileQInvF002 lam) y := by
  have hf := profileQ_analyticAt lam (profileQInvF002 lam y)
  have hd : deriv (profileQF002 lam) (profileQInvF002 lam y) ≠ 0 := by
    rw [(profileQ_hasDerivAt (ne_of_gt hlam) _).deriv]
    exact ne_of_gt (profileQDerivative_pos hlam _)
  have hcomp : AnalyticAt ℝ (profileQInvF002 lam ∘ profileQF002 lam)
      (profileQInvF002 lam y) := by
    have heq : profileQInvF002 lam ∘ profileQF002 lam = id :=
      funext (profileQ_leftInverse hlam)
    rw [heq]
    exact analyticAt_id
  have hi := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hcomp
  rwa [profileQ_rightInverse hlam y] at hi

def signedProfileRF002 (lam y : ℝ) : ℝ := profilePInvF002 lam (Real.cos y)
def signedProfileUF002 (lam y : ℝ) : ℝ := profileQInvF002 lam (Real.cos (lam * y))
def profileDifferenceF002 (lam y : ℝ) : ℝ :=
  signedProfileRF002 lam y ^ 2 - signedProfileUF002 lam y ^ 2

theorem signedProfileR_analyticAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    AnalyticAt ℝ (signedProfileRF002 lam) y :=
  (profilePInv_analyticAt hlam _).comp Real.analyticAt_cos

theorem signedProfileU_analyticAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    AnalyticAt ℝ (signedProfileUF002 lam) y :=
  (profileQInv_analyticAt hlam _).comp
    (Real.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))

theorem profileDifference_analyticAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    AnalyticAt ℝ (profileDifferenceF002 lam) y :=
  ((signedProfileR_analyticAt hlam y).pow 2).sub ((signedProfileU_analyticAt hlam y).pow 2)

end
end IsingBulk.AnisoF002.Geometry
