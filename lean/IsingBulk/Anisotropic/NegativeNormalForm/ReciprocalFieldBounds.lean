import IsingBulk.Anisotropic.NegativeNormalForm.NormalizedMeanField

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

 theorem scalar_norm_lower_of_near_one (z : ℂ) (hz : ‖z-1‖≤1/2) : 1/2≤‖z‖ := by
  have hh := norm_sub_norm_le (1:ℂ) z
  rw [norm_one,norm_sub_rev] at hh
  linarith

 theorem scalar_inverse_norm_of_near_one (z : ℂ) (hz : ‖z-1‖≤1/2) : ‖z⁻¹‖≤2 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) (scalar_norm_lower_of_near_one z hz)
  simpa only [norm_inv,one_div,inv_div,inv_one,div_one,inv_inv] using hh

 theorem scalar_reciprocal_error (z : ℂ) (hz : ‖z-1‖≤1/2) : ‖1-z⁻¹‖≤2*‖z-1‖ := by
  have hzn : z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (scalar_norm_lower_of_near_one z hz))
  have he : 1-z⁻¹=(z-1)*z⁻¹ := by field_simp
  rw [he,norm_mul]
  exact (mul_le_mul_of_nonneg_left (scalar_inverse_norm_of_near_one z hz) (norm_nonneg _)).trans_eq (mul_comm _ _)

 theorem scalar_inverse_difference (z w : ℂ) (hz : ‖z-1‖≤1/2) (hw : ‖w-1‖≤1/2) :
    ‖z⁻¹-w⁻¹‖≤4*‖z-w‖ := by
  have hzn : z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (scalar_norm_lower_of_near_one z hz))
  have hwn : w≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (scalar_norm_lower_of_near_one w hw))
  have he : z⁻¹-w⁻¹= z⁻¹*(w-z)*w⁻¹ := by field_simp
  rw [he,norm_mul,norm_mul,norm_sub_rev w z]
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_right (scalar_inverse_norm_of_near_one z hz) (norm_nonneg (z-w)))
    (scalar_inverse_norm_of_near_one w hw) (norm_nonneg _) (by positivity : 0≤2*‖z-w‖)
  nlinarith

def reciprocalError {n : ℕ} (S : Config n) : Config n := fun i => 1-(S i)⁻¹

 theorem reciprocalError_norm_le {n : ℕ} (S : Config n) (hS : ‖S-1‖≤1/2) :
    ‖reciprocalError S‖≤2*‖S-1‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact (scalar_reciprocal_error (S i) ((norm_le_pi_norm (S-1) i).trans hS)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm (S-1) i) (by norm_num))

 theorem reciprocalError_lipschitz {n : ℕ} (S Q : Config n) (hS : ‖S-1‖≤1/2) (hQ : ‖Q-1‖≤1/2) :
    ‖reciprocalError S-reciprocalError Q‖≤4*‖S-Q‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have he : (reciprocalError S-reciprocalError Q) i=(Q i)⁻¹-(S i)⁻¹ := by
    simp only [reciprocalError,Pi.sub_apply]
    ring
  rw [he,norm_sub_rev]
  exact (scalar_inverse_difference (S i) (Q i) ((norm_le_pi_norm (S-1) i).trans hS)
    ((norm_le_pi_norm (Q-1) i).trans hQ)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm (S-Q) i) (by norm_num))

 theorem reciprocalError_analyticAt {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : E → Config n) (x : E) (hS : AnalyticAt ℂ S x) (hb : ‖S x-1‖≤1/2) :
    AnalyticAt ℂ (fun y => reciprocalError (S y)) x := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_const.sub ((analyticAt_pi_iff.mp hS i).inv ?_)
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (scalar_norm_lower_of_near_one (S x i) ((norm_le_pi_norm (S x-1) i).trans hb)))

 theorem normalizedMeanField_analyticAt {n : ℕ} (hn : n≠0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E → Config n) (x : E) (hA : AnalyticAt ℂ A x) (hb : ‖A x‖≤1/2) :
    AnalyticAt ℂ (fun y => normalizedMeanField (A y)) x := by
  have hm : AnalyticAt ℂ (fun y => mean (A y)) x := by
    simpa only [Function.comp_def,meanCLM_apply] using ((meanCLM n).analyticAt (A x)).comp (f := A) hA
  have hp : AnalyticAt ℂ (fun y => project (A y)) x := by
    simpa only [Function.comp_def,projectCLM_apply] using ((projectCLM n).analyticAt (A x)).comp (f := A) hA
  have hden : 1-mean (A x)≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (meanField_denominator_lower hn (A x) hb))
  exact ((analyticAt_const.sub hm).inv hden).smul hp

end
end IsingBulk.Anisotropic.NegativeNormalForm
