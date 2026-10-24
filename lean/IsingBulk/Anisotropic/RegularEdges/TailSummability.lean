import IsingBulk.Anisotropic.RegularEdges.ParticleMajorant
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

 theorem particleEdgeMajorant_polynomial_summable {r C M : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (j : ℕ) :
    Summable (fun N : ℕ => (N:ℝ)^j*particleEdgeMajorant r C M N) := by
  have hEven : Summable (fun n : ℕ => ((2*n:ℕ):ℝ)^j*particleEdgeMajorant r C M (2*n)) := by
    simpa [mul_pow,mul_assoc] using
      (evenEdgeMajorant_polynomial_summable hr hr1 hC hM j).mul_left (2^j)
  have hOdd : Summable (fun n : ℕ => ((2*n+1:ℕ):ℝ)^j*particleEdgeMajorant r C M (2*n+1)) := by
    have ha := oddEdgeMajorant_polynomial_summable hr hr1 hC hM j
    have hz := oddEdgeMajorant_polynomial_summable hr hr1 hC hM 0
    apply (((ha.mul_left (2^j)).add hz).mul_left (2^(j-1))).of_nonneg_of_le
      (fun n => mul_nonneg (by positivity) (particleEdgeMajorant_nonneg hr.le hC.le hM.le _))
    intro n
    have hE : 0≤oddEdgeMajorant r C M n := by unfold oddEdgeMajorant; positivity
    have hh := mul_le_mul_of_nonneg_right
      (add_pow_le (show 0≤2*(n:ℝ) by positivity) (by norm_num : (0:ℝ)≤1) j) hE
    simp only [particleEdgeMajorant_odd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      pow_zero,one_mul]
    convert hh using 1
    ring
  let e : ℕ ≃ Fin 2 × ℕ := (Nat.divModEquiv 2).trans (Equiv.prodComm _ _)
  apply e.symm.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => by
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (particleEdgeMajorant_nonneg hr.le hC.le hM.le _))).mpr
  constructor
  · intro i
    fin_cases i
    · simpa [e,Nat.divModEquiv,Nat.mul_comm] using hEven
    · simpa [e,Nat.divModEquiv,Nat.mul_comm] using hOdd
  · exact hasSum_fintype _ |>.summable

end IsingBulk.Anisotropic.RegularEdges
