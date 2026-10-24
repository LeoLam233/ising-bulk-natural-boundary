import IsingBulk.Anisotropic.FormFactors.CanceledLattice
import IsingBulk.Tail.IndexedPairCounting

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.Tail
open scoped BigOperators

theorem index_pair_card_sum (N : ℕ) :
    (∑ i : Fin N, (Finset.univ.filter (fun j : Fin N => i<j)).card) = N.choose 2 := by
  have hc := orderedIndexPairs_card (Finset.univ : Finset (Fin N))
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  rw [← hc]
  simp only [orderedIndexPairs,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]

theorem anisotropicCanceledPairs_factor {N : ℕ} (B : ℝ) (u y : Fin N → ℂ) :
    anisotropicCanceledPairs B u y = (B:ℂ)^(N.choose 2)*canceledPairProduct u y := by
  simp only [anisotropicCanceledPairs,canceledPairProduct,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.prod_pow_eq_pow_sum,index_pair_card_sum]

theorem anisotropy_choose_exponent (N : ℕ) :
    (N:ℝ)/2 + (N.choose 2:ℝ) = (N:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  ring

theorem anisotropy_choose_power (N : ℕ) {B : ℝ} (hB : 0 < B) :
    B^((N:ℝ)/2)*B^(N.choose 2) = anisotropyPower N B := by
  rw [← Real.rpow_natCast,← Real.rpow_add hB,anisotropy_choose_exponent]
  rfl
end
end IsingBulk.Anisotropic.FormFactors
