import IsingBulk.Anisotropic.RegularEdges.ComplexAngularIdentity
import IsingBulk.Anisotropic.RegularEdges.NumeratorJets

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

theorem smallRoot_eq_continuedRoot {W : ℂ} (hW : 0<W.im) : smallRoot W=continuedRoot W := by
  rw [continuedRoot_eq_interiorRoot hW]
  exact smallRoot_eq_of_quadratic (Or.inl hW.ne') (interiorRoot_quadratic W)
    (interiorRoot_norm_lt_one hW)

theorem canceledPair_unit_eq_angularRootPair (a b : ℝ) (r s : ℂ) :
    canceledPair (limitingAngle a) (limitingAngle b) r s = angularRootPair r s (a:ℂ) (b:ℂ) := by
  calc
    _ = (-(limitingAngle a-limitingAngle b)^2/(limitingAngle a*limitingAngle b))*
        (r*s/(1-r*s)^2) := by unfold canceledPair; simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ = _ := by rw [physical_unit_pair_numerator]; unfold angularRootPair; push_cast; ring

theorem indexed_pairProduct_eq_list (N : ℕ) (K : ℂ → ℂ → ℂ) (q : Fin N → ℂ) :
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), K (q i) (q j)) =
      IsingBulk.Schur.pairProduct K (List.ofFn q) := by
  induction N with
  | zero => simp [IsingBulk.Schur.pairProduct]
  | succ N ih =>
    rw [List.ofFn_succ,IsingBulk.Schur.pairProduct,List.map_ofFn,List.prod_ofFn]
    rw [← ih (fun i => q i.succ)]
    simp only [Finset.prod_filter]
    rw [Fin.prod_univ_succ]
    simp [Fin.prod_univ_succ,Fin.succ_pos]

theorem edgeCircleCanceledKernel_unit (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (a c : ℝ) :
    edgeCircleCanceledKernel b B u (limitingAngle a) (limitingAngle c) =
      B u*angularRootPair (edgeParamRoot b B u a) (edgeParamRoot b B u c) (a:ℂ) (c:ℂ) := by
  simp only [edgeCircleCanceledKernel,edgeCircleRoot,edgeCircleW_unit,edgeParamRoot]
  rw [canceledPair_unit_eq_angularRootPair]

theorem edgeNumerator_eq_indexed {N : ℕ} (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : Fin N → ℝ) :
    edgeNumerator b B S u (List.ofFn q) =
      (B u)^(N.choose 2)*(S u)⁻¹^N *
        (∏ i, 2*edgeParamRoot b B u (q i)/(1-edgeParamRoot b B u (q i)^2)) *
        (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
          angularRootPair (edgeParamRoot b B u (q i)) (edgeParamRoot b B u (q j)) (q i:ℂ) (q j:ℂ)) := by
  unfold edgeNumerator radialEdgePairProduct
  simp only [List.map_ofFn,Function.comp_def,radialEdgeY_one,List.prod_ofFn]
  rw [← indexed_pairProduct_eq_list]
  simp_rw [edgeCircleCanceledKernel_unit]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_pow_eq_pow_sum,
    FormFactors.index_pair_card_sum]
  have hone (i : Fin N) : edgeOneBody b B S u (q i) =
      (S u)⁻¹*(2*edgeParamRoot b B u (q i)/(1-edgeParamRoot b B u (q i)^2)) := by
    unfold edgeOneBody
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [hone]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

theorem transferW_eq_edgeParamW {lam b : ℝ} {B : ℂ → ℂ} {z u : ℂ}
    (hB : B u=spectralT lam z/spectralS z)
    (he : edgeMapV lam 1 z=(b:ℂ)+u) (q : ℝ) :
    transferW lam z (q:ℂ)=edgeParamW b B u q := by
  unfold edgeParamW
  rw [hB,← he]
  unfold transferW edgeMapV
  simp only [Complex.ofReal_cos,div_eq_mul_inv]
  ring

theorem transferRoot_eq_edgeParamRoot {lam b : ℝ} {B : ℂ → ℂ} {z u : ℂ}
    (hB : B u=spectralT lam z/spectralS z)
    (he : edgeMapV lam 1 z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : ℝ) :
    transferRoot lam z (q:ℂ)=edgeParamRoot b B u q := by
  unfold transferRoot edgeParamRoot
  rw [transferW_eq_edgeParamW hB he]
  apply smallRoot_eq_continuedRoot
  have hc : 0≤1-Real.cos q := sub_nonneg.mpr (Real.cos_le_one q)
  have hm := mul_nonneg hBi.le hc
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,
    sub_zero,mul_zero]
  linarith

theorem complexAngularWeight_eq_edgeNumerator {N : ℕ} {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hB : B u=spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam 1 z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : Fin N → ℝ) :
    complexAngularWeight lam z (fun i => (q i:ℂ))=edgeNumerator b B S u (List.ofFn q) := by
  rw [edgeNumerator_eq_indexed]
  unfold complexAngularWeight
  simp_rw [transferRoot_eq_edgeParamRoot hB he hu hBi]
  rw [hB,hS]

end
end IsingBulk.Anisotropic.RegularEdges
