import IsingBulk.Joint.Negative.FamilyParameterQuotient
import IsingBulk.Anisotropic.NegativeNormalForm.UniformScalarRescaling

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_hessian_rescaling (B : ℂ × E→ℂ) (phi : ℝ)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) :
    ∃r : ℝ,0<r ∧ ∀eta∈P,∀d : ℂ,‖d‖<r →
      centralHessian (familyMember B eta) phi d≠0 ∧
      ‖(Complex.sqrt (centralHessian (familyMember B eta) phi d))⁻¹-1‖≤1/64 ∧
      ‖(Complex.sqrt (centralHessian (familyMember B eta) phi d))⁻¹‖≤9/8 := by
  let G : Set (ℂ × E) := {q | centralHessian (familyMember B q.2) phi q.1≠0 ∧
    ‖(Complex.sqrt (centralHessian (familyMember B q.2) phi q.1))⁻¹-1‖<1/64}
  have hcenter (eta : E) (heta : eta∈P) : (0,eta)∈interior G := by
    apply mem_interior_iff_mem_nhds.mpr
    have hh := family_hessian_analyticAt B phi eta (hB eta heta)
    have hs : AnalyticAt ℂ (fun q : ℂ × E=>Complex.sqrt (centralHessian (familyMember B q.2) phi q.1))
        (0,eta) := sqrt_analyticAt_one.comp_of_eq hh (centralHessian_zero _ phi)
    have hi := hs.inv (by simp [centralHessian_zero])
    exact (hh.continuousAt.eventually_ne (by simp only [centralHessian_zero,ne_eq,one_ne_zero,not_false_eq_true])).and
      (((hi.continuousAt.sub continuousAt_const).norm).eventually_lt_const
        (by simp [centralHessian_zero]))
  obtain ⟨r,hr,hG⟩ := compact_product_tube hP (isOpen_interior : IsOpen (interior G)) hcenter
  refine ⟨r,hr,?_⟩
  intro eta heta d hd
  have hh := interior_subset (s:=G) (hG eta heta d hd)
  refine ⟨hh.1,hh.2.le,?_⟩
  have ht := norm_le_norm_sub_add ((Complex.sqrt (centralHessian (familyMember B eta) phi d))⁻¹) 1
  rw [norm_one] at ht
  linarith [hh.2]

end
end IsingBulk.Joint.Negative
