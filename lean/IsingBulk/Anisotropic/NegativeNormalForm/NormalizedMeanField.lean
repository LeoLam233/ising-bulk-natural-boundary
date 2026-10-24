import IsingBulk.Anisotropic.NegativeNormalForm.MeanUniformBounds
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedUniformEstimates

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

/-- Dimension-normalized mean field, with its common scalar coefficient removed. -/
def normalizedMeanField {n : ℕ} (A : Config n) : Config n := (1-mean A)⁻¹ • project A

 theorem mean_one_sub_reciprocal {n : ℕ} (hn : n≠0) (S : Config n) :
    1-mean (fun i => 1-(S i)⁻¹)=(∑ i, (S i)⁻¹)/(n:ℂ) := by
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
  simp only [mean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp
  ring

 theorem normalizedMeanField_eq_scaled_coefficients {n : ℕ} (hn : n≠0) (S : Config n) :
    normalizedMeanField (fun i => 1-(S i)⁻¹)=(n:ℂ) • meanCoefficients S := by
  rw [normalizedMeanField,mean_one_sub_reciprocal hn S]
  have hp (z : ℂ) (v : Config n) : project (z • v)=z • project v := by
    simp only [← projectCLM_apply,map_smul]
  unfold meanCoefficients
  have he : (fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹))=
      (∑ j, (S j)⁻¹)⁻¹ • (fun i => 1-(S i)⁻¹) := by
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [he,hp,smul_smul,inv_div]
  congr 1

 theorem norm_mean_sub_mean_le {n : ℕ} (hn : n≠0) (A B : Config n) :
    ‖mean A-mean B‖≤‖A-B‖ := by
  rw [← meanCLM_apply,← meanCLM_apply,← map_sub,meanCLM_apply]
  exact norm_mean_le hn _

 theorem meanField_denominator_lower {n : ℕ} (hn : n≠0) (A : Config n) (hA : ‖A‖≤1/2) :
    1/2≤‖1-mean A‖ := by
  have hh := norm_sub_norm_le (1:ℂ) (mean A)
  have hm := norm_mean_le hn A
  simp only [norm_one] at hh
  linarith

 theorem meanField_inverse_norm_le {n : ℕ} (hn : n≠0) (A : Config n) (hA : ‖A‖≤1/2) :
    ‖(1-mean A)⁻¹‖≤2 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) (meanField_denominator_lower hn A hA)
  simpa only [norm_inv,one_div,inv_div,inv_one,div_one,inv_inv] using hh

 theorem normalizedMeanField_norm_le {n : ℕ} (hn : n≠0) (A : Config n) (hA : ‖A‖≤1/2) :
    ‖normalizedMeanField A‖≤4*‖A‖ := by
  rw [normalizedMeanField,norm_smul]
  have hh := mul_le_mul (meanField_inverse_norm_le hn A hA) (norm_project_le hn A) (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  nlinarith

 theorem meanField_inverse_difference {n : ℕ} (hn : n≠0) (A B : Config n)
    (hA : ‖A‖≤1/2) (hB : ‖B‖≤1/2) :
    ‖(1-mean A)⁻¹-(1-mean B)⁻¹‖≤4*‖A-B‖ := by
  have hAn : 1-mean A≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (meanField_denominator_lower hn A hA))
  have hBn : 1-mean B≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (meanField_denominator_lower hn B hB))
  have he : (1-mean A)⁻¹-(1-mean B)⁻¹=(1-mean A)⁻¹*(mean A-mean B)*(1-mean B)⁻¹ := by
    field_simp
    ring
  rw [he,norm_mul,norm_mul]
  have hh := mul_le_mul
    (mul_le_mul (meanField_inverse_norm_le hn A hA) (norm_mean_sub_mean_le hn A B) (norm_nonneg _) (by norm_num : (0:ℝ)≤2))
    (meanField_inverse_norm_le hn B hB) (norm_nonneg _) (by positivity : 0≤2*‖A-B‖)
  nlinarith

 theorem normalizedMeanField_lipschitz {n : ℕ} (hn : n≠0) (A B : Config n)
    (hA : ‖A‖≤1/2) (hB : ‖B‖≤1/2) :
    ‖normalizedMeanField A-normalizedMeanField B‖≤8*‖A-B‖ := by
  have hp : project A-project B=project (A-B) := by
    simp only [← projectCLM_apply,map_sub]
  have he : normalizedMeanField A-normalizedMeanField B=
      (1-mean A)⁻¹ • (project A-project B)+((1-mean A)⁻¹-(1-mean B)⁻¹) • project B := by
    ext i
    simp only [normalizedMeanField,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  have hh := norm_add_le ((1-mean A)⁻¹ • (project A-project B)) (((1-mean A)⁻¹-(1-mean B)⁻¹) • project B)
  simp only [norm_smul] at hh
  have h1 := mul_le_mul (meanField_inverse_norm_le hn A hA) (norm_project_sub_le hn A B) (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have h2 := mul_le_mul (meanField_inverse_difference hn A B hA hB) (norm_project_le hn B) (norm_nonneg _) (by positivity : 0≤4*‖A-B‖)
  nlinarith [norm_nonneg (A-B)]

end
end IsingBulk.Anisotropic.NegativeNormalForm
