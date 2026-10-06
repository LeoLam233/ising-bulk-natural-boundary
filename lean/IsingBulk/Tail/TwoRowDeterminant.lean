import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic

/-! A genuine two-row phase update has the principal two-by-two
Jacobian determinant, regardless of its spectator columns. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem determinant_identity_except_two_rows {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (hij : i≠j)
    (hA : ∀ k : Fin N, k≠i → k≠j → ∀ l, A k l = if k=l then 1 else 0) :
    A.det = A i i*A j j-A i j*A j i := by
  let e : Fin 2 → Fin N := fun a => if a=0 then i else j
  let U : Matrix (Fin N) (Fin 2) ℝ := fun k a => if k=e a then 1 else 0
  let V : Matrix (Fin 2) (Fin N) ℝ := fun a l => A (e a) l - if e a=l then 1 else 0
  have hrep : A=1+U*V := by
    ext k l
    change A k l = (if k=l then 1 else 0) + ∑ a : Fin 2, U k a*V a l
    simp only [Fin.sum_univ_two,U,V,e,
      ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
    by_cases hki : k=i
    · subst k
      simp only [ite_true,hij,ite_false,one_mul,zero_mul,add_zero]
      ring
    · by_cases hkj : k=j
      · subst k
        simp only [ite_true,Ne.symm hij,ite_false,one_mul,zero_mul,zero_add]
        ring
      · rw [hA k hki hkj l]
        simp [hki,hkj]
  have hsmall : (1+V*U : Matrix (Fin 2) (Fin 2) ℝ)=fun a b => A (e a) (e b) := by
    ext a b
    have hsum : (∑ k : Fin N, V a k*U k b)=V a (e b) := by
      simp only [U,mul_ite,mul_one,mul_zero]
      simp
    change (if a=b then 1 else 0) + (∑ k : Fin N, V a k*U k b) = A (e a) (e b)
    rw [hsum]
    dsimp only [V]
    fin_cases a <;> fin_cases b <;> simp [e,hij,Ne.symm hij]
  conv_lhs => rw [hrep,Matrix.det_one_add_mul_comm,hsmall,Matrix.det_fin_two]
  simp only [e,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]

theorem continuousLinearMap_det_two_rows {N : ℕ}
    (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (i j : Fin N) (hij : i≠j)
    (hL : ∀ x : Fin N → ℝ, ∀ k : Fin N, k≠i → k≠j → L x k=x k) :
    L.det = L (Pi.single i 1) i*L (Pi.single j 1) j-
      L (Pi.single j 1) i*L (Pi.single i 1) j := by
  rw [← LinearMap.det_toMatrix']
  apply determinant_identity_except_two_rows _ i j hij
  intro k hki hkj l
  rw [LinearMap.toMatrix'_apply]
  change L (Pi.single l 1) k = _
  rw [hL _ k hki hkj]
  by_cases hkl : k=l
  · subst l; simp
  · simp [hkl]

end
end IsingBulk.Tail
