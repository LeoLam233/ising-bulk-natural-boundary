import IsingBulk.Tail.MicrocoreWindow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Common quadratic exponential budget for the actual microcore radius and
finite-order semantic/cutoff factors. -/
namespace IsingBulk.Tail
noncomputable section

theorem microcore_radius_inverse_quadratic {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 1 ≤ N → 0 < microcoreRadius A c N ∧
      (microcoreRadius A c N)⁻¹ ≤ Real.exp (B*(N:ℝ)^2) := by
  let B := |Real.log c|+A+5
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg (Real.log c)]
  refine ⟨B,hB,?_⟩
  intro N hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hNN : (N:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hb : 0 < microcoreRadius A c N := by unfold microcoreRadius; positivity
  refine ⟨hb,?_⟩
  have hci : c⁻¹ ≤ Real.exp |Real.log c| := by
    rw [← Real.exp_log hc,← Real.exp_neg]
    simp only [Real.log_exp]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have hnexp : (N:ℝ) ≤ Real.exp N := by have h := Real.add_one_le_exp (N:ℝ); linarith
  have he : (microcoreRadius A c N)⁻¹ = c⁻¹*(N:ℝ)*Real.exp ((A+4)*N) := by
    unfold microcoreRadius
    rw [inv_div,div_eq_mul_inv,mul_inv_rev,← Real.exp_neg]
    ring_nf
  rw [he]
  calc
    _ ≤ Real.exp |Real.log c| * Real.exp (N:ℝ) * Real.exp ((A+4)*N) := by gcongr
    _ = Real.exp (|Real.log c|+(A+5)*N) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (B*(N:ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      have h1 := le_mul_of_one_le_right (abs_nonneg (Real.log c)) hn2
      have h2 := mul_le_mul_of_nonneg_left hNN (show 0 ≤ A+5 by linarith)
      dsimp [B]
      nlinarith

theorem microcore_total_finite_cost {A c C E K : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hC : 1 ≤ C) (hE : 0 < E) (hK : 1 ≤ K) (J : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j ≤ J →
      ((N:ℝ)+1)^j*K^N*((microcoreRadius A c N)⁻¹)^j*
        (((2:ℝ)^J*C)^j*Real.exp (E*(N:ℝ)^2)) ≤ Real.exp (D*(N:ℝ)^2) := by
  obtain ⟨B,hB,hb⟩ := microcore_radius_inverse_quadratic hA hc
  let U : ℝ := 2^J*C
  have hU : 1 ≤ U := by
    dsimp [U]
    have hh : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    nlinarith
  have hlogU := Real.log_nonneg hU
  have hlogK := Real.log_nonneg hK
  let D := 2*(J:ℝ)+Real.log K+(J:ℝ)*B+(J:ℝ)*Real.log U+E+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro N hN j hj
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hNN : (N:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hjR : (j:ℝ)≤J := by exact_mod_cast hj
  obtain ⟨hbpos,hbinv⟩ := hb N hN
  have hpoly : ((N:ℝ)+1)^j ≤ Real.exp (2*(J:ℝ)*(N:ℝ)^2) := by
    have hbase : (N:ℝ)+1 ≤ Real.exp (2*N) := by
      have hh := Real.add_one_le_exp (2*(N:ℝ))
      linarith
    calc
      _ ≤ (Real.exp (2*N))^j := pow_le_pow_left₀ (by positivity) hbase j
      _ = Real.exp ((j:ℝ)*(2*N)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_right hjR (show 0 ≤ 2*(N:ℝ) by positivity)
        have h2 := mul_le_mul_of_nonneg_left hNN (show 0 ≤ 2*(J:ℝ) by positivity)
        nlinarith
  have hKpow : K^N ≤ Real.exp (Real.log K*(N:ℝ)^2) := by
    rw [← Real.exp_log (by linarith : 0<K),← Real.exp_nat_mul]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hNN hlogK
    nlinarith
  have hbpow : ((microcoreRadius A c N)⁻¹)^j ≤ Real.exp ((J:ℝ)*B*(N:ℝ)^2) := by
    calc
      _ ≤ (Real.exp (B*(N:ℝ)^2))^j := pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hbinv j
      _ = Real.exp ((j:ℝ)*(B*(N:ℝ)^2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hjR (mul_nonneg hB.le (sq_nonneg (N:ℝ)))
        nlinarith
  have hUpow : U^j ≤ Real.exp ((J:ℝ)*Real.log U*(N:ℝ)^2) := by
    rw [← Real.exp_log (by linarith : 0<U),← Real.exp_nat_mul]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hjR hlogU
    have h2 := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg J) hlogU) hn2
    nlinarith
  calc
    _ ≤ Real.exp (2*(J:ℝ)*(N:ℝ)^2)*Real.exp (Real.log K*(N:ℝ)^2)*
        Real.exp ((J:ℝ)*B*(N:ℝ)^2)*
        (Real.exp ((J:ℝ)*Real.log U*(N:ℝ)^2)*Real.exp (E*(N:ℝ)^2)) := by
      change ((N:ℝ)+1)^j*K^N*((microcoreRadius A c N)⁻¹)^j*(U^j*_) ≤ _
      gcongr
    _ ≤ Real.exp (D*(N:ℝ)^2) := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [D]
      nlinarith [sq_nonneg (N:ℝ)]

end
end IsingBulk.Tail
