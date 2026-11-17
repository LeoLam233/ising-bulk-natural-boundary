import IsingBulk.AnisoF002.Geometry.EndpointBoundary
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The actual anisotropic endpoint profiles are increasing bijections

F002 `eq:physicalPQ`, and the paragraphs before `thm:components` and
`eq:signed-profiles`.  These are the literal hyperbolic profiles; no
monotonicity or surjectivity premise is supplied by a caller.
The inverse functions use the same total `Function.invFun` convention as
the frozen domain definitions, and the inverse equations are proved.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open Filter Set

def profilePF002 (lam x : ℝ) : ℝ := Real.cosh x * Real.tanh (lam * x)
def profileQF002 (lam x : ℝ) : ℝ := Real.cosh (lam * x) * Real.tanh x
def profilePInvF002 (lam : ℝ) : ℝ → ℝ := Function.invFun (profilePF002 lam)
def profileQInvF002 (lam : ℝ) : ℝ → ℝ := Function.invFun (profileQF002 lam)

def profilePDerivativeF002 (lam x : ℝ) : ℝ :=
  Real.sinh x * Real.tanh (lam * x) +
    lam * Real.cosh x / Real.cosh (lam * x) ^ 2

theorem real_tanh_hasDerivAt_f002 (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x))
  convert hh using 1
  · funext y
    exact Real.tanh_eq_sinh_div_cosh y
  · congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem real_tanh_strictMono_f002 : StrictMono Real.tanh := by
  apply strictMono_of_hasDerivAt_pos real_tanh_hasDerivAt_f002
  intro x
  positivity

theorem profileP_hasDerivAt (lam x : ℝ) :
    HasDerivAt (profilePF002 lam) (profilePDerivativeF002 lam x) x := by
  have ht := (real_tanh_hasDerivAt_f002 (lam * x)).comp x (hasDerivAt_const_mul lam)
  convert (Real.hasDerivAt_cosh x).mul ht using 1
  · rfl
  · unfold profilePDerivativeF002
    simp only [Function.comp_apply]
    ring

theorem profilePDerivative_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    0 < profilePDerivativeF002 lam x := by
  have hp : 0 ≤ Real.sinh x * Real.sinh (lam * x) := by
    by_cases hx : 0 ≤ x
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr hx)
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hlam.le hx))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (Real.sinh_nonpos_iff.mpr (le_of_not_ge hx))
        (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hlam.le (le_of_not_ge hx)))
  have hfirst : 0 ≤ Real.sinh x * Real.tanh (lam * x) := by
    rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
    exact div_nonneg hp (Real.cosh_pos _).le
  have hsecond : 0 < lam * Real.cosh x / Real.cosh (lam * x) ^ 2 := by positivity
  exact add_pos_of_nonneg_of_pos hfirst hsecond

theorem profileP_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (profilePF002 lam) :=
  strictMono_of_hasDerivAt_pos (profileP_hasDerivAt lam) (profilePDerivative_pos hlam)

theorem profileP_continuous (lam : ℝ) : Continuous (profilePF002 lam) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (profileP_hasDerivAt lam x).continuousAt

theorem profileP_zero (lam : ℝ) : profilePF002 lam 0 = 0 := by
  simp only [profilePF002, mul_zero, Real.tanh_zero]

theorem profileP_neg (lam x : ℝ) : profilePF002 lam (-x) = -profilePF002 lam x := by
  simp only [profilePF002, mul_neg, Real.cosh_neg, Real.tanh_neg]

theorem profileP_linear_lower {lam x : ℝ} (hlam : 0 < lam) (hx : 1 ≤ x) :
    Real.tanh lam * x ≤ profilePF002 lam x := by
  have ht : 0 < Real.tanh lam := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hlam) (Real.cosh_pos lam)
  have hcosh : x ≤ Real.cosh x :=
    (Real.self_le_sinh_iff.mpr (by linarith)).trans (Real.sinh_lt_cosh x).le
  have htan : Real.tanh lam ≤ Real.tanh (lam * x) :=
    real_tanh_strictMono_f002.monotone (by nlinarith)
  calc
    Real.tanh lam * x ≤ Real.tanh lam * Real.cosh x := mul_le_mul_of_nonneg_left hcosh ht.le
    _ = Real.cosh x * Real.tanh lam := by ring
    _ ≤ profilePF002 lam x := mul_le_mul_of_nonneg_left htan (Real.cosh_pos x).le

theorem profileP_tendsto_atTop {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (profilePF002 lam) atTop atTop := by
  have ht : 0 < Real.tanh lam := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hlam) (Real.cosh_pos lam)
  have hlin : Tendsto (fun x : ℝ => Real.tanh lam * x) atTop atTop :=
    tendsto_id.const_mul_atTop ht
  apply tendsto_atTop_mono' atTop _ hlin
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact profileP_linear_lower hlam hx

theorem profileP_tendsto_atBot {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (profilePF002 lam) atBot atBot := by
  have hh := tendsto_neg_atTop_atBot.comp
    ((profileP_tendsto_atTop hlam).comp tendsto_neg_atBot_atTop)
  change Tendsto (fun x : ℝ => -profilePF002 lam (-x)) atBot atBot at hh
  simpa only [profileP_neg, neg_neg] using hh

theorem profileP_surjective {lam : ℝ} (hlam : 0 < lam) :
    Function.Surjective (profilePF002 lam) :=
  (profileP_continuous lam).surjective (profileP_tendsto_atTop hlam) (profileP_tendsto_atBot hlam)

theorem profileQ_eq_axis_exchange {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    profileQF002 lam x = profilePF002 lam⁻¹ (lam * x) := by
  unfold profileQF002 profilePF002
  rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

theorem profileQ_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (profileQF002 lam) := by
  intro x y hxy
  rw [profileQ_eq_axis_exchange (ne_of_gt hlam), profileQ_eq_axis_exchange (ne_of_gt hlam)]
  exact profileP_strictMono (inv_pos.mpr hlam) (mul_lt_mul_of_pos_left hxy hlam)

theorem profileQ_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (profileQF002 lam) := by
  have heq : profileQF002 lam = fun x => profilePF002 lam⁻¹ (lam * x) :=
    funext (profileQ_eq_axis_exchange (ne_of_gt hlam))
  rw [heq]
  exact (profileP_continuous lam⁻¹).comp (continuous_const.mul continuous_id)

theorem profileQ_surjective {lam : ℝ} (hlam : 0 < lam) :
    Function.Surjective (profileQF002 lam) := by
  intro y
  obtain ⟨x, hx⟩ := profileP_surjective (inv_pos.mpr hlam) y
  refine ⟨x / lam, ?_⟩
  rw [profileQ_eq_axis_exchange (ne_of_gt hlam)]
  have hcancel : lam * (x / lam) = x := by field_simp
  rw [hcancel, hx]

theorem profileP_rightInverse {lam : ℝ} (hlam : 0 < lam) :
    Function.RightInverse (profilePInvF002 lam) (profilePF002 lam) :=
  Function.rightInverse_invFun (profileP_surjective hlam)

theorem profileP_leftInverse {lam : ℝ} (hlam : 0 < lam) :
    Function.LeftInverse (profilePInvF002 lam) (profilePF002 lam) :=
  Function.leftInverse_invFun (profileP_strictMono hlam).injective

theorem profileQ_rightInverse {lam : ℝ} (hlam : 0 < lam) :
    Function.RightInverse (profileQInvF002 lam) (profileQF002 lam) :=
  Function.rightInverse_invFun (profileQ_surjective hlam)

theorem profileQ_leftInverse {lam : ℝ} (hlam : 0 < lam) :
    Function.LeftInverse (profileQInvF002 lam) (profileQF002 lam) :=
  Function.leftInverse_invFun (profileQ_strictMono hlam).injective

theorem profilePInv_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (profilePInvF002 lam) := by
  intro x y hxy
  apply (profileP_strictMono hlam).lt_iff_lt.mp
  rw [profileP_rightInverse hlam x, profileP_rightInverse hlam y]
  exact hxy

theorem profileQInv_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (profileQInvF002 lam) := by
  intro x y hxy
  apply (profileQ_strictMono hlam).lt_iff_lt.mp
  rw [profileQ_rightInverse hlam x, profileQ_rightInverse hlam y]
  exact hxy

theorem profilePInv_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (profilePInvF002 lam) :=
  (profilePInv_strictMono hlam).monotone.continuous_of_surjective
    (profileP_leftInverse hlam).surjective

theorem profileQInv_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (profileQInvF002 lam) :=
  (profileQInv_strictMono hlam).monotone.continuous_of_surjective
    (profileQ_leftInverse hlam).surjective

end
end IsingBulk.AnisoF002.Geometry
