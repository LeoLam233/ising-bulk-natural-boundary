import IsingBulk.Anisotropic.NegativeDominance.GaussianEntropyAbsorption

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail

/-- Sharp Gaussian moment maximization, proved for every index and order. -/
theorem gaussian_log_moment_bound {a : ℝ} (ha : 0<a) (N j : ℕ) :
    (j : ℝ)*Real.log N-a/2*(N : ℝ)^2≤
      (j : ℝ)/2*Real.log ((j : ℝ)+1)+|Real.log a|/2*j := by
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,Real.log_zero,mul_zero,zero_pow (by decide : 2≠0),sub_zero]
    have hlog : 0≤Real.log ((j : ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    positivity
  have hNr : (0 : ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hj : (0 : ℝ)≤j := Nat.cast_nonneg j
  have hj1 : (0 : ℝ)<(j : ℝ)+1 := by positivity
  have hq : 0<a*(N : ℝ)^2/((j : ℝ)+1) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div (by positivity) hj1.ne',Real.log_mul ha.ne' (by positivity),Real.log_pow] at hlog
  have ht := mul_le_mul_of_nonneg_left hlog hj
  have hfrac : (j : ℝ)/((j : ℝ)+1)≤1 := (div_le_one hj1).mpr (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hfrac (show 0≤a*(N : ℝ)^2 by positivity)
  have hprod' : (j : ℝ)*(a*(N : ℝ)^2/((j : ℝ)+1))≤a*(N : ℝ)^2 := by
    convert hprod using 1 <;> ring
  have habs := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log a)) hj
  nlinarith only [ht,hprod',habs,hj]

/-- Full infinite Gaussian moment sum with the sharp one-half coefficient.
The constant precedes every Taylor order. -/
theorem gaussian_log_moment_sum {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∃D : ℝ, 0<D ∧ ∀j : ℕ,
      Summable (fun N : ℕ => Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+C*((j : ℝ)+1))) ∧
      (∑' N : ℕ, Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+C*((j : ℝ)+1)))≤
        D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+(C+|Real.log a|/2)*((j : ℝ)+1)) := by
  let g : ℕ→ℝ := fun N => Real.exp (-(a/2)*(N : ℝ)^2)
  have hg : Summable g := by
    simpa [g] using summable_polynomial_gaussian 0 (by positivity : 0<a/2) 0
  have hg0 : 0<∑' N,g N :=
    (Real.exp_pos _).trans_le (hg.le_tsum 0 (fun _ _ => (Real.exp_pos _).le))
  refine ⟨∑' N,g N,hg0,fun j => ?_⟩
  let E : ℝ := ((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+(C+|Real.log a|/2)*((j : ℝ)+1)
  have hb (N : ℕ) : Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+C*((j : ℝ)+1))≤
      Real.exp E*g N := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := gaussian_log_moment_bound ha N (j+1)
    push_cast at hh
    rw [show (j : ℝ)+1+1=(j : ℝ)+2 by ring] at hh
    dsimp [E]
    linarith
  have hmaj := hg.mul_left (Real.exp E)
  have hs := hmaj.of_nonneg_of_le (fun N => (Real.exp_pos _).le) hb
  refine ⟨hs,?_⟩
  calc
    _≤∑' N,Real.exp E*g N := hs.tsum_le_tsum hb hmaj
    _=Real.exp E*(∑' N,g N) := tsum_mul_left
    _=_ := mul_comm _ _

end
end IsingBulk.Anisotropic.NegativeDominance
