import IsingBulk.Anisotropic.NegativeNormalForm.NormalizedMeanField
import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators Topology

def normalizedRankCoefficient (z : ℂ) : ℂ := (1+Complex.sqrt (1+z))⁻¹

def normalizedMeanCorrection {n : ℕ} (e w : Config n) : Config n :=
  w+(normalizedRankCoefficient (mean (e*e))*mean (w*e)) • e

 theorem normalizedMeanCorrection_scaled {n : ℕ} (hn : n≠0) (ell w : Config n) :
    normalizedMeanCorrection ((n:ℂ) • ell) w=meanCorrection ell w := by
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
  have hq : mean (((n:ℂ) • ell)*((n:ℂ) • ell))=(n:ℂ)*quadratic ell := by
    simp only [mean,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,quadratic]
    have he : (∑ i, ((n:ℂ)*ell i)*((n:ℂ)*ell i))=(n:ℂ)^2*∑ i, ell i^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    field_simp
  have hp : mean (w*((n:ℂ) • ell))=pairing w ell := by
    simp only [mean,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,pairing]
    have he : (∑ i, w i*((n:ℂ)*ell i))=(n:ℂ)*∑ i, w i*ell i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    field_simp
  ext i
  simp only [normalizedMeanCorrection,hq,hp,normalizedRankCoefficient,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,meanCorrection,rankOneCoefficient,div_eq_mul_inv]
  ring

 theorem normalizedRankCoefficient_norm_le (z : ℂ) : ‖normalizedRankCoefficient z‖≤1 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (one_le_norm_one_add_sqrt (1+z))
  simpa only [normalizedRankCoefficient,norm_inv,one_div,inv_one] using hh

 theorem normalizedRankCoefficient_analyticAt : AnalyticAt ℂ normalizedRankCoefficient 0 := by
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (1+z)) 0 :=
    sqrt_analyticAt_one.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  exact (analyticAt_const.add hs).inv (by simp)

 theorem normalizedRankCoefficient_uniform_lipschitz :
    ∃ r K : ℝ, 0<r ∧ 0<K ∧ ∀ z w : ℂ, ‖z‖<r → ‖w‖<r →
      ‖normalizedRankCoefficient z-normalizedRankCoefficient w‖≤K*‖z-w‖ := by
  have ha : AnalyticAt ℂ (fun p : ScalarTriple => normalizedRankCoefficient p.1) 0 :=
    normalizedRankCoefficient_analyticAt.fun_comp_of_eq (f := fun p : ScalarTriple => p.1) (analyticAt_fst (p := (0:ScalarTriple))) rfl
  obtain ⟨r,K,M,hr,hK,_hM,_ha,hLip⟩ := analytic_scalarTriple_uniform_lipschitz ha
  refine ⟨r,K,hr,hK,?_⟩
  intro z w hz hw
  simpa using hLip (z,(0,0)) (w,(0,0)) (by simpa using hz) (by simpa using hw)

 theorem normalizedRankCoefficient_uniform_analytic_lipschitz :
    ∃ r K : ℝ, 0<r ∧ 0<K ∧
      (∀ z : ℂ, ‖z‖<r → AnalyticAt ℂ normalizedRankCoefficient z) ∧
      (∀ z w : ℂ, ‖z‖<r → ‖w‖<r →
        ‖normalizedRankCoefficient z-normalizedRankCoefficient w‖≤K*‖z-w‖) := by
  have ha : AnalyticAt ℂ (fun p : ScalarTriple => normalizedRankCoefficient p.1) 0 :=
    normalizedRankCoefficient_analyticAt.fun_comp_of_eq (f := fun p : ScalarTriple => p.1)
      (analyticAt_fst (p := (0:ScalarTriple))) rfl
  obtain ⟨r,K,M,hr,hK,_hM,hall,hLip⟩ := analytic_scalarTriple_uniform_lipschitz ha
  refine ⟨r,K,hr,hK,?_,?_⟩
  · intro z hz
    exact ((hall (z,(0,0)) (by simpa using hz)).1).comp
      (f := fun w : ℂ => (w,((0:ℂ),(0:ℂ)))) (analyticAt_id.prod analyticAt_const)
  · intro z w hz hw
    simpa using hLip (z,(0,0)) (w,(0,0)) (by simpa using hz) (by simpa using hw)

 theorem mean_product_norm_le {n : ℕ} (hn : n≠0) (v w : Config n) :
    ‖mean (v*w)‖≤‖v‖*‖w‖ := (norm_mean_le hn _).trans (norm_mul_le v w)

 theorem mean_product_difference_le {n : ℕ} (hn : n≠0) (v w e f : Config n) :
    ‖mean (v*e)-mean (w*f)‖≤‖v-w‖*‖e‖+‖w‖*‖e-f‖ := by
  have he : v*e-w*f=(v-w)*e+w*(e-f) := by ring
  calc
    _ ≤ ‖v*e-w*f‖ := norm_mean_sub_mean_le hn _ _
    _ = ‖(v-w)*e+w*(e-f)‖ := by rw [he]
    _ ≤ ‖(v-w)*e‖+‖w*(e-f)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)

 theorem mean_square_difference_le {n : ℕ} (hn : n≠0) (e f : Config n) :
    ‖mean (e*e)-mean (f*f)‖≤(‖e‖+‖f‖)*‖e-f‖ := by
  have he : e*e-f*f=(e+f)*(e-f) := by ring
  calc
    _ ≤ ‖e*e-f*f‖ := norm_mean_sub_mean_le hn _ _
    _ = ‖(e+f)*(e-f)‖ := by rw [he]
    _ ≤ ‖e+f‖*‖e-f‖ := norm_mul_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)

end
end IsingBulk.Anisotropic.NegativeNormalForm
