import IsingBulk.Joint.Negative.FamilyQuadratic
import IsingBulk.Anisotropic.NegativeNormalForm.MeanEnergyBound

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem compact_family_mean_separable_refined_bound (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀eta∈P,∀ n : ℕ, ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖d‖<r → ‖v‖<r → ZeroMean v →
      ‖mean (fun i => v i*rootScalar (familyMember B eta) phi hphi (t,(d,v i)))‖≤
        L*(‖d‖+‖v‖)/(n:ℝ)*absoluteEnergy v := by
  obtain ⟨r,L,hr,hL,hroot⟩ := compact_family_root_quadratic B phi hphi hP hB hBn
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta n t d v ht hd hv hmean
  apply mean_separable_energy_bound v _ (rootScalar (familyMember B eta) phi hphi (t,(d,0))) _ hmean
  intro i
  have h := hroot eta heta (t,(d,v i)) (max_lt ht (max_lt hd ((norm_le_pi_norm v i).trans_lt hv)))
  apply h.trans
  change L*(‖d‖+‖v i‖)*‖v i‖≤L*(‖d‖+‖v‖)*‖v i‖
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_right (norm_le_pi_norm v i) ‖d‖) hL.le) (norm_nonneg _)

end
end IsingBulk.Joint.Negative
