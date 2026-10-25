import IsingBulk.Joint.Geometry.ExactSpectrum
import IsingBulk.Anisotropic.RegularEdges.SmallRoot

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic.RegularEdges

/-- Denominator-safe canonical root: the axis is defined by the polynomial, not division. -/
def canonicalRoot (K : Coupling) (q : ℂ) : ℂ :=
  if S K=0 then 0 else smallRoot ((A K-T K*Complex.cos q)/S K)

theorem transferGap_ne_zero {K : Coupling} (hK : K∉spectralSet) (q : ℝ) :
    A K-T K*Complex.cos (q:ℂ)≠0 := by
  intro h
  apply hK
  refine ⟨0,by norm_num,Real.cos q,⟨Real.neg_one_le_cos q,Real.cos_le_one q⟩,?_⟩
  simpa only [Complex.ofReal_zero,mul_zero,zero_add,Complex.ofReal_cos] using sub_eq_zero.mp h

theorem transfer_mem_smallRootDomain {K : Coupling} (hK : K∉spectralSet)
    (hS : S K≠0) (q : ℝ) : (A K-T K*Complex.cos (q:ℂ))/S K ∈ SmallRootDomain := by
  by_contra h
  simp only [SmallRootDomain,Set.mem_ofPred_eq,not_or,not_not,not_lt] at h
  let W := (A K-T K*Complex.cos (q:ℂ))/S K
  have he : (W.re:ℂ)=W := Complex.ext (by simp) (by simpa [W] using h.1.symm)
  apply hK
  refine ⟨W.re,⟨h.2.2,h.2.1⟩,Real.cos q,⟨Real.neg_one_le_cos q,Real.cos_le_one q⟩,?_⟩
  rw [he,Complex.ofReal_cos]
  dsimp [W]
  field_simp
  ring

theorem canonicalRoot_spec {K : Coupling} (hK : K∉spectralSet) (q : ℝ) :
    rootPolynomial K (q:ℂ) (canonicalRoot K (q:ℂ))=0 ∧ ‖canonicalRoot K (q:ℂ)‖<1 := by
  by_cases hS : S K=0
  · simp [canonicalRoot,hS,rootPolynomial]
  · have hs := smallRoot_spec (transfer_mem_smallRootDomain hK hS q)
    simp only [canonicalRoot,ite_eq_right hS]
    refine ⟨?_,hs.2⟩
    dsimp [rootPolynomial]
    have he := hs.1
    field_simp at he
    linear_combination he

theorem canonicalRoot_unique {K : Coupling} (hK : K∉spectralSet) (q : ℝ)
    {rho : ℂ} (he : rootPolynomial K (q:ℂ) rho=0) (hn : ‖rho‖<1) :
    rho=canonicalRoot K (q:ℂ) := by
  by_cases hS : S K=0
  · simp only [canonicalRoot,ite_eq_left hS]
    have hg := transferGap_ne_zero hK q
    simp only [rootPolynomial,hS,zero_mul,add_zero,zero_sub] at he
    exact (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left (mul_ne_zero (by norm_num : (2:ℂ)≠0) hg)
  · simp only [canonicalRoot,ite_eq_right hS]
    apply (smallRoot_eq_of_quadratic (transfer_mem_smallRootDomain hK hS q) ?_ hn).symm
    dsimp [rootPolynomial] at he
    field_simp
    linear_combination he

end
end IsingBulk.Joint
