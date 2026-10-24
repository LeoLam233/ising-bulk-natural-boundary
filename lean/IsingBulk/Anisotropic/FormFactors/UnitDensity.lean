import IsingBulk.Anisotropic.FormFactors.PhysicalContourBridge
import IsingBulk.Anisotropic.FormFactors.PairPower

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

theorem unit_onebody {B C S : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    limitingAngle q * (2*(root B C q:ℂ)/
      ((S:ℂ)*limitingAngle q*(1-(root B C q:ℂ)*(root B C q:ℂ)))) =
    ((S*Real.sinh (gamma B C q))⁻¹:ℝ) := by
  have hu := root_bounds hB hgap q
  have hg := Real.sinh_pos_iff.mpr (gamma_pos hB hgap q)
  have hrel : 2*root B C q*Real.sinh (gamma B C q) = 1-(root B C q)^2 := by
    rw [Real.sinh_eq,root,Real.exp_neg]
    field_simp
  have hrelC : 2*(root B C q:ℂ)*(Real.sinh (gamma B C q):ℂ) =
      1-(root B C q:ℂ)^2 := by exact_mod_cast hrel
  have hy := norm_ne_zero_iff.mp ((limitingAngle_norm q).trans_ne (by norm_num : (1:ℝ) ≠ 0))
  have hroot : (root B C q:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
  rw [← pow_two,← hrelC]
  push_cast
  field_simp

theorem unit_pair_product {N : ℕ} {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B)
    (q : Fin N → ℝ) :
    anisotropicCanceledPairs B (fun i => realContourRoot B C (limitingAngle (q i)))
      (fun i => limitingAngle (q i)) = (B^(N.choose 2)*pairProduct B C q:ℝ) := by
  rw [anisotropicCanceledPairs_factor]
  simp only [realContourRoot_unit hB hgap,canceledPairProduct,canceled_pair hB hgap,
    pairProduct,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_prod]

theorem unit_onebody_product {N : ℕ} {B C S : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B)
    (q : Fin N → ℝ) :
    coordinateProduct (fun i => limitingAngle (q i)) *
      (∏ i,2*realContourRoot B C (limitingAngle (q i))/
        ((S:ℂ)*limitingAngle (q i)*(1-realContourRoot B C (limitingAngle (q i))*
          realContourRoot B C (limitingAngle (q i))))) =
    ((S^N)⁻¹*(∏ i,(Real.sinh (gamma B C (q i)))⁻¹):ℝ) := by
  simp only [realContourRoot_unit hB hgap,coordinateProduct,← Finset.prod_mul_distrib]
  simp_rw [unit_onebody hB hgap]
  simp only [mul_inv_rev,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,Complex.ofReal_prod,Complex.ofReal_mul]
  push_cast
  ring

/-- The complete unit-contour density with its Jacobian angular product.
All B and S powers are retained before temperature normalization. -/
theorem canceledLatticeDensity_unit {N : ℕ} {B C S : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B)
    (q : Fin N → ℝ) (v : ℤ × ℤ) :
    coordinateProduct (fun i => limitingAngle (q i))*
      canceledLatticeDensity B C (S:ℂ) (fun i => limitingAngle (q i)) v =
    (B^(N.choose 2)*(S^N)⁻¹*(∏ i,(Real.sinh (gamma B C (q i)))⁻¹)*
      pairProduct B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
      Complex.exp (Complex.I*(v.2.natAbs:ℂ)*(∑ i,(q i:ℂ))) := by
  unfold canceledLatticeDensity
  dsimp only
  have hroot : coordinateProduct (fun i => realContourRoot B C (limitingAngle (q i))) =
      (rootProduct B C q:ℂ) := by
    simp only [coordinateProduct,rootProduct,realContourRoot_unit hB hgap,Complex.ofReal_prod]
  rw [hroot]
  have hang := physical_angle_coordinateProduct_zpow q (v.2.natAbs:ℤ)
  simp only [zpow_natCast,Int.cast_natCast] at hang
  rw [hang]
  rw [unit_pair_product hB hgap q]
  have hbody := unit_onebody_product (S := S) hB hgap q
  push_cast at hbody ⊢
  linear_combination (B:ℂ)^(N.choose 2)*(pairProduct B C q:ℂ)*
    (rootProduct B C q:ℂ)^v.1.natAbs*
    Complex.exp (Complex.I*(v.2.natAbs:ℂ)*(∑ i,(q i:ℂ)))*hbody
end
end IsingBulk.Anisotropic.FormFactors
