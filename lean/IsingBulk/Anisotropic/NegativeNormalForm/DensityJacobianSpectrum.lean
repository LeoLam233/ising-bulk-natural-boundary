import IsingBulk.Anisotropic.NegativeNormalForm.UniformDerivativeBounds
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

/-- Eigenvalues of a constrained operator are controlled in the ambient norm,
without paying for the operator norm of its coordinate chart. -/
theorem lifted_eigenvalue_sub_one_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E→L[ℂ]E) (K : F→L[ℂ]F) (J : F→L[ℂ]E)
    (hJ : Function.Injective J) (hinter : ∀v,L (J v)=J (K v))
    {eps : ℝ} (hL : ‖L-ContinuousLinearMap.id ℂ E‖≤eps)
    {mu : ℂ} (hmu : Module.End.HasEigenvalue K.toLinearMap mu) : ‖mu-1‖≤eps := by
  obtain ⟨v,hv⟩ := hmu.exists_hasEigenvector
  have hjv : J v≠0 := by
    intro h
    exact hv.2 (hJ (by simpa using h))
  have he : (L-ContinuousLinearMap.id ℂ E) (J v)=(mu-1) • J v := by
    simp only [sub_apply,ContinuousLinearMap.id_apply,hinter]
    rw [show K v=mu • v from hv.apply_eq_smul,map_smul,sub_smul,one_smul]
  have hh := (L-ContinuousLinearMap.id ℂ E).le_opNorm (J v)
  rw [he,norm_smul] at hh
  have ht := hh.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  nlinarith [norm_pos_iff.mpr hjv]

theorem multiset_product_norm_bounds {a b : ℝ} (ha : 0≤a)
    (s : Multiset ℂ) (h : ∀z∈s,a≤‖z‖ ∧ ‖z‖≤b) :
    a^s.card≤‖s.prod‖ ∧ ‖s.prod‖≤b^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    have hz := h z (by simp)
    have hs := ih (fun w hw => h w (by simp [hw]))
    simp only [Multiset.card_cons,Multiset.prod_cons,norm_mul,pow_succ]
    constructor
    · nlinarith [mul_le_mul hz.1 hs.1 (pow_nonneg ha _) (norm_nonneg z)]
    · have hb : 0≤b := (norm_nonneg z).trans hz.2
      nlinarith [mul_le_mul hz.2 hs.2 (norm_nonneg s.prod) hb]

/-- Uniform two-sided determinant bounds from ambient near-identity control. -/
theorem lifted_det_norm_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (L : E→L[ℂ]E) (K : F→L[ℂ]F) (J : F→L[ℂ]E)
    (hJ : Function.Injective J) (hinter : ∀v,L (J v)=J (K v))
    {eps : ℝ} (heps : eps≤1) (hL : ‖L-ContinuousLinearMap.id ℂ E‖≤eps) :
    (1-eps)^(Module.finrank ℂ F)≤‖K.toLinearMap.det‖ ∧
      ‖K.toLinearMap.det‖≤(1+eps)^(Module.finrank ℂ F) := by
  have hsplit := IsAlgClosed.splits K.toLinearMap.charpoly
  have hc : K.toLinearMap.charpoly.roots.card=Module.finrank ℂ F :=
    hsplit.natDegree_eq_card_roots.symm.trans K.toLinearMap.charpoly_natDegree
  rw [Module.End.det_eq_prod_roots_charpoly_of_splits hsplit,←hc]
  apply multiset_product_norm_bounds (sub_nonneg.mpr heps)
  intro mu hmu
  have he := lifted_eigenvalue_sub_one_bound L K J hJ hinter hL
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly K.toLinearMap mu).mpr
      ((Polynomial.mem_roots K.toLinearMap.charpoly_monic.ne_zero).mp hmu))
  have hu := norm_le_norm_sub_add mu 1
  have hl := norm_sub_norm_le (1:ℂ) mu
  rw [norm_sub_rev] at hl
  norm_num only [norm_one] at hu hl
  constructor <;> linarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
