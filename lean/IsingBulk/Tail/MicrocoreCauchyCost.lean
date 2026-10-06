import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Scalar finite-jet cost of the actual protected fixed-phase microcore disk. -/
namespace IsingBulk.Tail
noncomputable section

def microcoreCauchyRadius (r A C : ℝ) (N : ℕ) : ℝ :=
  min (r/2) (Real.exp (-A*N)/(4*N*C^N))

theorem microcore_cauchy_radius_inverse_bound {r A C : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 1 ≤ N →
      0 < microcoreCauchyRadius r A C N ∧
      (microcoreCauchyRadius r A C N)⁻¹ ≤ Real.exp (B*(N:ℝ)^2) := by
  let k := 4+A+Real.log C
  let B := |Real.log ((r/2)⁻¹)|+k
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hk : 0 < k := by dsimp [k]; linarith
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg (Real.log ((r/2)⁻¹))]
  refine ⟨B,hB,?_⟩
  intro N hN
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hn2 : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hnle : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hc0 : 0 < C := by linarith
  have hr2 : 0 < r/2 := by linarith
  have hden : 0 < (4:ℝ)*N*C^N := by positivity
  have hpos : 0 < microcoreCauchyRadius r A C N :=
    lt_min hr2 (div_pos (Real.exp_pos _) hden)
  refine ⟨hpos,?_⟩
  have hconst : (r/2)⁻¹ ≤ Real.exp (B*(N:ℝ)^2) := by
    conv_lhs => rw [← Real.exp_log (inv_pos.mpr hr2)]
    apply Real.exp_le_exp.mpr
    have hBN : B ≤ B*(N:ℝ)^2 := le_mul_of_one_le_right hB.le hn2
    have hl := le_abs_self (Real.log ((r/2)⁻¹))
    dsimp [B] at hBN
    linarith
  have hpower : C^N=Real.exp ((N:ℝ)*Real.log C) := by rw [Real.exp_nat_mul,Real.exp_log hc0]
  have hlin : (4:ℝ)*N ≤ Real.exp (4*N) := by
    have hh := Real.add_one_le_exp ((4:ℝ)*N)
    linarith
  have hother : (Real.exp (-A*N)/(4*N*C^N))⁻¹ ≤ Real.exp (B*(N:ℝ)^2) := by
    rw [inv_div,div_eq_mul_inv,← Real.exp_neg]
    have he : -(-A*(N:ℝ))=A*N := by ring
    rw [he]
    calc
      4*(N:ℝ)*C^N*Real.exp (A*N) ≤ Real.exp (4*N)*Real.exp ((N:ℝ)*Real.log C)*Real.exp (A*N) := by
        rw [← hpower]
        gcongr
      _ = Real.exp (k*N) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; dsimp [k]; ring
      _ ≤ Real.exp (B*(N:ℝ)^2) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hnle hk.le
        have hb : k ≤ B := by dsimp [B]; linarith [abs_nonneg (Real.log ((r/2)⁻¹))]
        have hh2 := mul_le_mul_of_nonneg_right hb (sq_nonneg (N:ℝ))
        linarith
  unfold microcoreCauchyRadius
  by_cases h : r/2 ≤ Real.exp (-A*N)/(4*N*C^N)
  · rw [min_eq_left h]
    exact hconst
  · rw [min_eq_right (le_of_not_ge h)]
    exact hother

/-- Every fixed finite derivative window has a common quadratic exponential
budget on the exact source radius. Constants precede all particle numbers. -/
theorem microcore_cauchy_finite_cost {r A C E : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hC : 1 ≤ C) (hE : 0 < E) (J : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j ≤ J →
      (j.factorial : ℝ)*(4*Real.exp (E*(N:ℝ)^2+A*N))/
        (microcoreCauchyRadius r A C N)^j ≤ Real.exp (D*(N:ℝ)^2) := by
  obtain ⟨B,hB,hδ⟩ := microcore_cauchy_radius_inverse_bound hr hA hC
  let F : ℝ := 4*(J.factorial : ℝ)
  let Q : ℝ := E+A+(J:ℝ)*B
  let D : ℝ := Q+|Real.log F|+1
  have hF : 0 < F := by dsimp [F]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro N hN j hj
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  obtain ⟨hδpos,hδinv⟩ := hδ N hN
  have hfac : (j.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hj
  have hjR : (j:ℝ) ≤ J := by exact_mod_cast hj
  have hpow : ((microcoreCauchyRadius r A C N)⁻¹)^j ≤
      Real.exp ((J:ℝ)*B*(N:ℝ)^2) := by
    calc
      _ ≤ (Real.exp (B*(N:ℝ)^2))^j := pow_le_pow_left₀ (inv_nonneg.mpr hδpos.le) hδinv j
      _ = Real.exp ((j:ℝ)*(B*(N:ℝ)^2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hjR (mul_nonneg hB.le (sq_nonneg (N:ℝ)))
        nlinarith
  have hamp : Real.exp (E*(N:ℝ)^2+A*N) ≤ Real.exp ((E+A)*(N:ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hNN hA
    nlinarith
  calc
    _ = (4*(j.factorial:ℝ))*Real.exp (E*(N:ℝ)^2+A*N)*
        ((microcoreCauchyRadius r A C N)⁻¹)^j := by
      rw [div_eq_mul_inv,← inv_pow]
      ring
    _ ≤ (4*(J.factorial:ℝ))*Real.exp ((E+A)*(N:ℝ)^2)*
        Real.exp ((J:ℝ)*B*(N:ℝ)^2) := by gcongr
    _ = Real.exp (Real.log F+Q*(N:ℝ)^2) := by
      rw [Real.exp_add,Real.exp_log hF,mul_assoc (4*(J.factorial:ℝ)),← Real.exp_add]
      congr 1
      dsimp [Q]
      ring
    _ ≤ Real.exp (D*(N:ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      have hl := le_abs_self (Real.log F)
      have hh := le_mul_of_one_le_right (abs_nonneg (Real.log F)) hn2
      dsimp [D]
      nlinarith

end
end IsingBulk.Tail
