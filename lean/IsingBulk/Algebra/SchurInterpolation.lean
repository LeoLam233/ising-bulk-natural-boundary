import IsingBulk.Algebra.SchurPfaffian
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! Exact polynomial interpolation for the general Schur induction. -/
namespace IsingBulk.Schur
noncomputable section
open Polynomial Finset

theorem monic_ratio_partial_fractions {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (hv : Set.InjOn v s) (P : F[X]) (hP : P.Monic)
    (hdeg : P.degree = s.card) (a : F) (ha : ∀ i ∈ s, a ≠ v i) :
    P.eval a / (Lagrange.nodal s v).eval a =
      1 + ∑ i ∈ s, Lagrange.nodalWeight s v i * (a-v i)⁻¹ * P.eval (v i) := by
  have hd : (P - Lagrange.nodal s v).degree < s.card := by
    rw [← hdeg]
    exact degree_sub_lt_left (by rw [hdeg, Lagrange.degree_nodal]) hP.ne_zero
      (by rw [hP.leadingCoeff, (Lagrange.nodal_monic (s := s) (v := v)).leadingCoeff])
  have hi : P - Lagrange.nodal s v = Lagrange.interpolate s v (fun i => P.eval (v i)) :=
    Lagrange.eq_interpolate_of_eval_eq _ hv hd (fun i hi => by
      rw [eval_sub, Lagrange.eval_nodal_at_node hi, sub_zero])
  have he := congrArg (fun Q : F[X] => Q.eval a) hi
  rw [eval_sub, Lagrange.eval_interpolate_not_at_node _ ha] at he
  apply (div_eq_iff (Lagrange.eval_nodal_not_at_node ha)).mpr
  linear_combination he

def schurWeight {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (j : ι) : F :=
  ∏ k ∈ s.erase j, (x j + x k) / (x j - x k)

theorem schur_residue_weight {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) {j : ι} (hj : j ∈ s) :
    Lagrange.nodalWeight s (fun i => -x i) j * (Lagrange.nodal s x).eval (-x j) =
      -(2*x j) * schurWeight s x j := by
  rw [Lagrange.eval_nodal, ← Finset.mul_prod_erase s (fun k => -x j - x k) hj]
  unfold Lagrange.nodalWeight schurWeight
  rw [show -x j - x j = -(2*x j) by ring]
  rw [← mul_assoc, mul_comm _ (-(2*x j)), mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [show -x j - -x k = -(x j - x k) by ring, inv_neg]
  rw [show -x j - x k = -(x j + x k) by ring]
  simp only [neg_mul_neg, div_eq_mul_inv]
  ring

theorem schur_partial_fractions {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (hx : Set.InjOn x s)
    (a : F) (ha : ∀ i ∈ s, a + x i ≠ 0) :
    (∏ i ∈ s, (a-x i)/(a+x i)) =
      1 - ∑ i ∈ s, (2*x i/(a+x i)) * schurWeight s x i := by
  have hneg : Set.InjOn (fun i => -x i) s := fun i hi j hj h => hx hi hj (neg_injective h)
  have hnot : ∀ i ∈ s, a ≠ -x i := by
    intro i hi hh
    apply ha i hi
    rw [hh, neg_add_cancel]
  have h := monic_ratio_partial_fractions s (fun i => -x i) hneg (Lagrange.nodal s x)
    Lagrange.nodal_monic Lagrange.degree_nodal a hnot
  rw [Lagrange.eval_nodal, Lagrange.eval_nodal, ← Finset.prod_div_distrib] at h
  simp only [sub_neg_eq_add] at h
  have hs : (∑ i ∈ s, Lagrange.nodalWeight s (fun i => -x i) i * (a+x i)⁻¹ *
      (Lagrange.nodal s x).eval (-x i)) =
      -(∑ i ∈ s, (2*x i/(a+x i)) * schurWeight s x i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (Lagrange.nodalWeight s (fun i => -x i) i *
          (Lagrange.nodal s x).eval (-x i)) * (a+x i)⁻¹ := by ring
      _ = _ := by rw [schur_residue_weight s x hi]; ring
  rw [hs] at h
  simpa only [sub_eq_add_neg] using h

theorem schur_weights_sum {F ι : Type*} [Field F] [CharZero F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (hx : Set.InjOn x s)
    (h0 : ∀ i ∈ s, x i ≠ 0) (hodd : Odd s.card) :
    ∑ i ∈ s, schurWeight s x i = 1 := by
  have h := schur_partial_fractions s x hx 0 (by simpa using h0)
  have hp : (∏ i ∈ s, (0-x i)/(0+x i)) = (-1 : F) := by
    calc
      _ = ∏ _i ∈ s, (-1 : F) := Finset.prod_congr rfl (fun i hi => by simp [h0 i hi])
      _ = _ := by rw [Finset.prod_const, hodd.neg_one_pow]
  have hs : (∑ i ∈ s, (2*x i/(0+x i)) * schurWeight s x i) =
      2 * ∑ i ∈ s, schurWeight s x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp [h0 i hi]
  rw [hp, hs] at h
  apply mul_left_cancel₀ (by norm_num : (2 : F) ≠ 0)
  linear_combination h

/-- The scalar odd-cardinality identity which supplies the Schur expansion weights. -/
theorem schur_weighted_identity {F ι : Type*} [Field F] [CharZero F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (hx : Set.InjOn x s)
    (h0 : ∀ i ∈ s, x i ≠ 0) (hodd : Odd s.card)
    (a : F) (ha : ∀ i ∈ s, a+x i ≠ 0) :
    (∏ i ∈ s, (a-x i)/(a+x i)) =
      ∑ i ∈ s, ((a-x i)/(a+x i)) * schurWeight s x i := by
  rw [schur_partial_fractions s x hx a ha, ← schur_weights_sum s x hx h0 hodd,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [ha i hi]
  ring

end
end IsingBulk.Schur
