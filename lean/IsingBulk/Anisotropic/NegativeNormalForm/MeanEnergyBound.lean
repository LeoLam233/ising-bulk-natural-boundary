import IsingBulk.Anisotropic.NegativeNormalForm.RootPairBounds
import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy
import IsingBulk.Anisotropic.NegativeNormalForm.MeanUniformBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

/-- Cancellation of the actual common root value in the zero-mean hyperplane. -/
theorem mean_separable_energy_bound {n : ℕ} (v S : Config n) (a : ℂ) (L : ℝ)
    (hv : ZeroMean v) (hS : ∀ i, ‖S i-a‖≤L*‖v i‖) :
    ‖mean (fun i => v i*S i)‖≤L/(n:ℝ)*absoluteEnergy v := by
  have he : (∑ i, v i*S i)=∑ i, v i*(S i-a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,show ∑ i,v i=0 from hv]
    simp
  have hb : ‖∑ i, v i*(S i-a)‖≤L*absoluteEnergy v := by
    apply (norm_sum_le _ _).trans
    calc
      ∑ i, ‖v i*(S i-a)‖ ≤ ∑ i, L*‖v i‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hS i) (norm_nonneg _)).trans_eq (by ring)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  rw [mean,norm_div,he]
  have hn : ‖(n:ℂ)‖=(n:ℝ) := by simp
  rw [hn]
  exact (div_le_div_of_nonneg_right hb (Nat.cast_nonneg n)).trans_eq (by ring)

theorem actual_mean_separable_refined_bound (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ n : ℕ, ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖d‖<r → ‖v‖<r → ZeroMean v →
      ‖mean (fun i => v i*rootScalar B phi hphi (t,(d,v i)))‖≤
        L*(‖d‖+‖v‖)/(n:ℝ)*absoluteEnergy v := by
  obtain ⟨r,L,hr,hL,hroot⟩ := phaseRootEnergy_quadratic_control B phi hphi hB hBn
  refine ⟨r,L,hr,hL,?_⟩
  intro n t d v ht hd hv hmean
  apply mean_separable_energy_bound v _ (rootScalar B phi hphi (t,(d,0))) _ hmean
  intro i
  have h := hroot (t,(d,v i)) (max_lt ht (max_lt hd ((norm_le_pi_norm v i).trans_lt hv)))
  apply h.trans
  change L*(‖d‖+‖v i‖)*‖v i‖≤L*(‖d‖+‖v‖)*‖v i‖
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_right (norm_le_pi_norm v i) ‖d‖) hL.le) (norm_nonneg _)

end
end IsingBulk.Anisotropic.NegativeNormalForm
