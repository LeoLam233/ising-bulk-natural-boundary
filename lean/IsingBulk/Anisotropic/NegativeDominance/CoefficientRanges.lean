import IsingBulk.Anisotropic.NegativeDominance.ResonantMiddleIndices
import IsingBulk.Anisotropic.NegativeDominance.GaussianRemainderDominance

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- An internal exact decomposition interface. This is not an assumption of
coefficient dominance: the four actual range/error terms must be constructed
from the physical periods. All scalar comparison and selection is downstream. -/
def HasCoefficientRanges (coeff : ℕ→ℂ) (B rootB : ℂ→ℂ) (phi : ℝ)
    (p : ℕ) (a D C : ℝ) (eta : ℕ→ℝ) (j : ℕ) : Prop :=
  ∃L : ℕ,∃low middleError high analyticError : ℂ,
    (L : ℝ)≤Real.log j ∧
    coeff j=low+(∑i∈resonantMiddleIndices p j,physicalModel B rootB phi (resonantParticle p i) j)+
      middleError+high+analyticError ∧
    ‖low‖≤D*(L : ℝ)^3*((L : ℝ)^3/a)^j ∧
    ‖middleError‖≤eta j*(∑i∈resonantMiddleIndices p j,‖physicalModel B rootB phi (resonantParticle p i) j‖) ∧
    ‖high‖≤D*Real.exp ((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32) ∧
    ‖analyticError‖≤D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+C*((j : ℝ)+1))

/-- The elementary complex triangle estimate keeps all phases and every term. -/
theorem complete_coefficient_triangle {I : Finset ℕ} {k : ℕ} (hk : k∈I)
    (f : ℕ→ℂ) (coeff low middle high analytic : ℂ)
    (heq : coeff=low+(∑i∈I,f i)+middle+high+analytic) :
    ‖f k‖≤‖coeff‖+‖low‖+(∑i∈I.erase k,‖f i‖)+‖middle‖+‖high‖+‖analytic‖ := by
  classical
  have he : coeff-f k=low+(∑i∈I.erase k,f i)+middle+high+analytic := by
    rw [heq,←Finset.add_sum_erase I f hk]
    ring
  have hnorm : ‖coeff-f k‖≤‖low‖+(∑i∈I.erase k,‖f i‖)+‖middle‖+‖high‖+‖analytic‖ := by
    rw [he]
    calc
      _ ≤ ‖low+(∑i∈I.erase k,f i)+middle+high‖+‖analytic‖ := norm_add_le _ _
      _ ≤ ‖low+(∑i∈I.erase k,f i)+middle‖+‖high‖+‖analytic‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖low+(∑i∈I.erase k,f i)‖+‖middle‖+‖high‖+‖analytic‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖low‖+‖∑i∈I.erase k,f i‖)+‖middle‖+‖high‖+‖analytic‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sum_le _ _
  have hh := norm_sub_norm_le (f k) coeff
  rw [norm_sub_rev] at hh
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
