import IsingBulk.Anisotropic.NegativeDominance.GaussianEntropyAbsorption
import IsingBulk.Anisotropic.RegularEdges.ParticleMajorant

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges

/-- The actual matched-pair numerator majorant has one common Gaussian
bound for every particle index, including both parities and small indices. -/
theorem particleEdgeMajorant_gaussian {r C M : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) :
    ∃a E : ℝ,0<a ∧ 0<E ∧ ∀N : ℕ,
      particleEdgeMajorant r C M N≤Real.exp (-a*(N : ℝ)^2+E) := by
  let k : ℝ := -2*Real.log r
  let A : ℝ := Real.log (2*M^2*C)-2*Real.log r
  let D : ℝ := |A|+2+|Real.log M|
  have hk : 0<k := by dsimp [k]; nlinarith [Real.log_neg hr hr1]
  have hD : 0≤D := by dsimp [D]; positivity
  obtain ⟨E,hE,hEg⟩ := gaussian_entropy_global k 1 D hk (by norm_num) hD
  have hpair (n : ℕ) :
      evenEdgeMajorant r C M n≤Real.exp (-(k/2)*(n : ℝ)^2+E) ∧
      oddEdgeMajorant r C M n≤Real.exp (-(k/2)*(n : ℝ)^2+E) := by
    have he := evenEdgeMajorant_exp_bound hr hC hM n
    have hent := hEg n
    have hAn := mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg n)
    have hMn : 0≤|Real.log M| *(n : ℝ) := by positivity
    have hnp : 0<(2*(n : ℝ)+1) := by positivity
    have hmult : M*(2*(n : ℝ)+1)≤Real.exp (|Real.log M|+2*n) := by
      calc
        _=Real.exp (Real.log M+Real.log (2*(n : ℝ)+1)) := by
          rw [Real.exp_add,Real.exp_log hM,Real.exp_log hnp]
        _≤_ := Real.exp_le_exp.mpr (by
          have hh := Real.log_le_sub_one_of_pos hnp
          linarith only [hh,le_abs_self (Real.log M)])
    constructor
    · apply he.trans (Real.exp_le_exp.mpr ?_)
      change A*n-k*(n : ℝ)^2+n*Real.log ((n : ℝ)+1)≤_
      dsimp [D] at hent
      nlinarith only [hent,hAn,hMn,abs_nonneg A,abs_nonneg (Real.log M),Nat.cast_nonneg (α := ℝ) n]
    · apply (oddEdgeMajorant_le_even hr.le hr1.le hC.le hM.le n).trans
      apply (mul_le_mul hmult he (by unfold evenEdgeMajorant; positivity) (Real.exp_pos _).le).trans
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      change |Real.log M|+2*n+(A*n-k*(n : ℝ)^2+n*Real.log ((n : ℝ)+1))≤_
      dsimp [D] at hent
      nlinarith only [hent,hAn,hMn,abs_nonneg A]
  refine ⟨k/16,E+k/8,by positivity,by positivity,fun N => ?_⟩
  have hbase : particleEdgeMajorant r C M N≤Real.exp (-(k/2)*((N/2 : ℕ) : ℝ)^2+E) := by
    unfold particleEdgeMajorant
    split
    · exact (hpair (N/2)).1
    · exact (hpair (N/2)).2
  apply hbase.trans (Real.exp_le_exp.mpr ?_)
  have hN : (N : ℝ)≤2*((N/2 : ℕ) : ℝ)+1 := by exact_mod_cast (show N≤2*(N/2)+1 by omega)
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg N
  have hdiv : (0 : ℝ)≤(N/2 : ℕ) := Nat.cast_nonneg _
  have hs : (N : ℝ)^2≤8*((N/2 : ℕ) : ℝ)^2+2 := by
    nlinarith only [hN,hN0,hdiv,sq_nonneg (2*((N/2 : ℕ) : ℝ)-1)]
  have hh := mul_le_mul_of_nonneg_left hs hk.le
  nlinarith only [hh]

end
end IsingBulk.Anisotropic.NegativeDominance
