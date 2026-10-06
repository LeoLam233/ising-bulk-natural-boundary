import IsingBulk.First.ResidueAlgebra

/-! Exact source density symmetries, separate from the integral bridge. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem sourceS_neg (s : ℂ) : sourceS (-s) = -sourceS s := by
  simp [sourceS, neg_add_rev, add_comm]

theorem dispersion_neg (x y s : ℂ) : dispersion (-x) (-y) (-s) = -dispersion x y s := by
  simp only [dispersion, sourceS_neg, inv_neg]
  ring

theorem coordinateProduct_neg {N : ℕ} (hN : Even N) (x : Fin N → ℂ) :
    coordinateProduct (fun i => -x i) = coordinateProduct x := by
  simp only [coordinateProduct, Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
    hN.neg_one_pow, one_mul]

theorem pairKernel_neg (a b : ℂ) : pairKernel (-a) (-b) = -pairKernel a b := by
  simp only [pairKernel, neg_mul_neg]
  ring

theorem doublePairProduct_neg {N : ℕ} (x y : Fin N → ℂ) :
    pairProduct (fun i => -x i) * pairProduct (fun i => -y i) = pairProduct x * pairProduct y := by
  unfold pairProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [pairKernel_neg, pairKernel_neg, neg_mul_neg]

theorem commonDensity_neg {N : ℕ} (hN : Even N) (s : ℂ) (x y : Fin N → ℂ) :
    commonDensity (-s) (fun i => -x i) (fun i => -y i) = commonDensity s x y := by
  unfold commonDensity
  rw [doublePairProduct_neg]
  simp_rw [dispersion_neg, inv_neg]
  rw [Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin, hN.neg_one_pow, one_mul]

theorem doubleDensity_neg {N : ℕ} (hN : Even N) (s : ℂ) (x y : Fin N → ℂ) :
    doubleDensity (-s) (fun i => -x i) (fun i => -y i) = doubleDensity s x y := by
  unfold doubleDensity
  rw [coordinateProduct_neg hN, coordinateProduct_neg hN, commonDensity_neg hN]

theorem sourceS_conjugate (s : ℂ) : sourceS (star s) = star (sourceS s) := by
  simp [sourceS]

theorem dispersion_conjugate (x y s : ℂ) :
    dispersion (star x) (star y) (star s) = star (dispersion x y s) := by
  simp [dispersion, sourceS]

theorem coordinateProduct_conjugate {N : ℕ} (x : Fin N → ℂ) :
    coordinateProduct (fun i => star (x i)) = star (coordinateProduct x) := by
  simp [coordinateProduct]

theorem pairProduct_conjugate {N : ℕ} (x : Fin N → ℂ) :
    pairProduct (fun i => star (x i)) = star (pairProduct x) := by
  simp [pairProduct, pairKernel]

theorem doubleDensity_conjugate {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    doubleDensity (star s) (fun i => star (x i)) (fun i => star (y i)) =
      star (doubleDensity s x y) := by
  simp [doubleDensity, commonDensity, coordinateProduct, pairProduct, pairKernel, dispersion, sourceS]

end
end IsingBulk.First
