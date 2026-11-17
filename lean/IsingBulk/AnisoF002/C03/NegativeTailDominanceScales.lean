import IsingBulk.AnisoF002.C03.NegativeSelectedModelGrowth

/-!
# All low, analytic and high particle scales are below the selected peak

The three complete-range majorants are compared with the same actual-model
lower exponent.  The growth constant is fixed before the order threshold.
The final inequality beats any prescribed geometric Taylor bound.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

def selectedMainExponent (D : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.log j) - D * j

def completeLowExponent (A : ℝ) (j : ℕ) : ℝ :=
  2 * (j : ℝ) * Real.log (Real.log j) + A * j + A

def completeAnalyticExponent (A : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A

def completeHighExponent (A : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) * Real.log j - (j : ℝ) / 2 * Real.log (Real.log j) -
    (j : ℝ) / 8 * Real.sqrt (Real.log j) + A * j + A

theorem log_le_sixteenth_of_large {x : ℝ} (hx : 256 ≤ x) :
    Real.log x ≤ x / 16 := by
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_pos.mpr hx0
  have hs2 := Real.sq_sqrt hx0.le
  have hs16 : 16 ≤ Real.sqrt x := by nlinarith
  have hroot : Real.sqrt x ≤ x / 16 := by nlinarith
  have hh := log_le_half_of_pos hs
  rw [Real.log_sqrt hx0.le] at hh
  linarith

theorem log_nat_succ_le_log_add_one {j : ℕ} (hj : 0 < j) :
    Real.log ((j + 1 : ℕ) : ℝ) ≤ Real.log j + 1 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have harg : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by push_cast; linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)) harg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hj0.ne'] at hh
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem complete_tail_exponents_below_main {A D : ℝ} {j : ℕ}
    (hj : 0 < j) (ht : 256 ≤ Real.log j)
    (hlinear : 32 * (A + D + 1) ≤ Real.log j)
    (hroot : 256 ≤ Real.sqrt (Real.log j))
    (hrootlinear : 16 * (A + D + 1) ≤ Real.sqrt (Real.log j)) :
    completeLowExponent A j ≤ selectedMainExponent D j - j + A ∧
    completeAnalyticExponent A j ≤ selectedMainExponent D j - j + A ∧
    completeHighExponent A j ≤ selectedMainExponent D j - j + A := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hll := mul_le_mul_of_nonneg_left (log_log_le_sixteenth ht) hj0
  have hlin := mul_le_mul_of_nonneg_left hlinear hj0
  have hlogj1 := mul_le_mul_of_nonneg_left (log_nat_succ_le_log_add_one hj) hj0
  have hrootlog := log_le_sixteenth_of_large hroot
  rw [Real.log_sqrt (show 0 ≤ Real.log j by linarith)] at hrootlog
  have hrootlogj := mul_le_mul_of_nonneg_left hrootlog hj0
  have hrootlinj := mul_le_mul_of_nonneg_left hrootlinear hj0
  dsimp [completeLowExponent, completeAnalyticExponent, completeHighExponent, selectedMainExponent]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem selected_exponent_beats_geometric {D M R : ℝ} (hD : 0 ≤ D)
    (hM : 0 < M) (hR : 0 < R) {j : ℕ} (hj : 0 < j)
    (ht : 256 ≤ Real.log j)
    (hbig : 32 * (D + |Real.log R| + |Real.log M| + 4) ≤ Real.log j) :
    M / R ^ j < Real.exp (selectedMainExponent D j) / 2 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hll := mul_le_mul_of_nonneg_left (log_log_le_sixteenth ht) hj0.le
  have hbigj := mul_le_mul_of_nonneg_left hbig hj0.le
  have habsR := abs_nonneg (Real.log R)
  have habsM := abs_nonneg (Real.log M)
  have hmain : (j : ℝ) * (|Real.log R| + |Real.log M| + 4) ≤ selectedMainExponent D j := by
    dsimp [selectedMainExponent]
    have hDj := mul_nonneg hD hj0.le
    have hRj := mul_nonneg habsR hj0.le
    have hMj := mul_nonneg habsM hj0.le
    nlinarith
  have hMabs : Real.log M ≤ (j : ℝ) * |Real.log M| :=
    (le_abs_self _).trans (by nlinarith)
  have hRabs := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log R)) hj0.le
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogbound : Real.log ((M / R ^ j) * 2) < selectedMainExponent D j := by
    rw [Real.log_mul (by positivity : M / R ^ j ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hM.ne' (pow_ne_zero _ hR.ne'), Real.log_pow]
    nlinarith
  have he := Real.exp_lt_exp.mpr hlogbound
  rw [Real.exp_log (by positivity : 0 < (M / R ^ j) * 2)] at he
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr he

theorem exists_complete_tail_domination_threshold {A D M R : ℝ}
    (hD : 0 ≤ D) (hM : 0 < M) (hR : 0 < R) :
    ∃ T : ℝ, 0 < T ∧ ∀ j : ℕ, T ≤ Real.log j →
      Real.exp (completeLowExponent A j) ≤ Real.exp (selectedMainExponent D j) / 64 ∧
      Real.exp (completeAnalyticExponent A j) ≤ Real.exp (selectedMainExponent D j) / 64 ∧
      Real.exp (completeHighExponent A j) ≤ Real.exp (selectedMainExponent D j) / 64 ∧
      M / R ^ j < Real.exp (selectedMainExponent D j) / 2 := by
  let Q : ℝ := max 256 (16 * (A + D + 1))
  let T : ℝ := max 256 (max (32 * (A + D + 1))
    (max (Q ^ 2) (max (A + Real.log 64) (32 * (D + |Real.log R| + |Real.log M| + 4)))))
  refine ⟨T, (by norm_num : (0 : ℝ) < 256).trans_le (le_max_left _ _), ?_⟩
  intro j hjT
  have ht : 256 ≤ Real.log j := (le_max_left _ _).trans hjT
  have hj : 0 < j := by
    by_contra hh
    have hz : j = 0 := by omega
    norm_num [hz] at ht
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlinear : 32 * (A + D + 1) ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hjT)
  have hQ2 : Q ^ 2 ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hjT))
  have hsmall : A + Real.log 64 ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hjT)))
  have hbig : 32 * (D + |Real.log R| + |Real.log M| + 4) ≤ Real.log j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hjT)))
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hsqrt : Q ≤ Real.sqrt (Real.log j) := by
    have hh := Real.sq_sqrt (show 0 ≤ Real.log j by linarith)
    have hs := Real.sqrt_nonneg (Real.log j)
    nlinarith
  have hroot : 256 ≤ Real.sqrt (Real.log j) := (le_max_left _ _).trans hsqrt
  have hrootlinear : 16 * (A + D + 1) ≤ Real.sqrt (Real.log j) := (le_max_right _ _).trans hsqrt
  obtain ⟨hlow, hanalytic, hhigh⟩ := complete_tail_exponents_below_main hj ht hlinear hroot hrootlinear
  have horder : A + Real.log 64 ≤ (j : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos hj0
    linarith
  have hbound {X : ℝ} (hX : X ≤ selectedMainExponent D j - j + A) :
      Real.exp X ≤ Real.exp (selectedMainExponent D j) / 64 := by
    calc
      _ ≤ Real.exp (selectedMainExponent D j - Real.log 64) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 64)]
  exact ⟨hbound hlow, hbound hanalytic, hbound hhigh,
    selected_exponent_beats_geometric hD hM hR hj ht hbig⟩

end
end IsingBulk.AnisoF002.NegativeHT
