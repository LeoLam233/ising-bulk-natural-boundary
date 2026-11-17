import IsingBulk.AnisoF002.C03.NegativeCompleteMiddleModel

/-!
# Uniform smallness of every middle competitor and first-winding error

The comparison is simultaneous over the complete physical particle window.
Only one threshold is needed after the fixed constants are chosen.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

def modelCompetitorFactor (d : ℝ) (j : ℕ) : ℝ :=
  2 * (Real.exp (-(d ^ 2 * Real.log j) / 8) /
    (1 - Real.exp (-(d ^ 2 * Real.log j) / 8)))

theorem modelCompetitorFactor_small {d : ℝ} {j : ℕ}
    (hd : 1 ≤ d) (hj : 8 * Real.log 64 ≤ Real.log j) :
    0 ≤ modelCompetitorFactor d j ∧ modelCompetitorFactor d j ≤ 1 / 16 := by
  let r : ℝ := Real.exp (-(d ^ 2 * Real.log j) / 8)
  have hlog64 : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have hlogj : 0 ≤ Real.log j := by linarith
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hd2 hlogj
  have hr64 : r ≤ 1 / 64 := by
    calc
      _ ≤ Real.exp (-Real.log 64) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 64)]; norm_num
  have hr : 0 < r := Real.exp_pos _
  have hden : 0 < 1 - r := by linarith
  change 0 ≤ 2 * (r / (1 - r)) ∧ 2 * (r / (1 - r)) ≤ 1 / 16
  constructor
  · positivity
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    linarith

theorem complete_middle_first_error_small {E N : ℝ} {j : ℕ}
    (hE : 0 ≤ E) (hN : 0 ≤ N) (hlog : 0 < Real.log j)
    (hwindow : N ^ 2 ≤ highParticleThreshold j)
    (hlarge : (64 * E) ^ 4 ≤ Real.log j) :
    E * N / Real.sqrt ((j : ℝ) + 1) ≤ 1 / 64 := by
  have hs : 0 < Real.sqrt (Real.log j) := Real.sqrt_pos.mpr hlog
  have hs2 := Real.sq_sqrt hlog.le
  have hEsq : (64 * E) ^ 2 ≤ Real.sqrt (Real.log j) := by nlinarith [sq_nonneg (64 * E)]
  have hwindow' : N ^ 2 * Real.sqrt (Real.log j) ≤ (j : ℝ) :=
    (le_div_iff₀ hs).mp hwindow
  have hm := mul_le_mul_of_nonneg_left hEsq (sq_nonneg N)
  have ht : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have ht2 := Real.sq_sqrt (show 0 ≤ (j : ℝ) + 1 by positivity)
  have hsq : (64 * E * N) ^ 2 ≤ (Real.sqrt ((j : ℝ) + 1)) ^ 2 := by nlinarith
  have hh := (sq_le_sq₀ (by positivity : 0 ≤ 64 * E * N) ht.le).mp hsq
  apply (div_le_iff₀ ht).mpr
  linarith

theorem exists_uniform_middle_smallness_threshold {E : ℝ} (hE : 0 ≤ E) :
    ∃ T : ℝ, 0 < T ∧ ∀ j : ℕ, T ≤ Real.log j →
      (∀ d : ℝ, 1 ≤ d → 0 ≤ modelCompetitorFactor d j ∧ modelCompetitorFactor d j ≤ 1 / 16) ∧
      ∀ N : ℝ, 0 ≤ N → N ^ 2 ≤ highParticleThreshold j →
        E * N / Real.sqrt ((j : ℝ) + 1) ≤ 1 / 64 := by
  let T : ℝ := max 1 (max (8 * Real.log 64) ((64 * E) ^ 4))
  refine ⟨T, (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _), ?_⟩
  intro j hj
  have hlog : 0 < Real.log j := (by norm_num : (0 : ℝ) < 1).trans_le ((le_max_left _ _).trans hj)
  have hgeo : 8 * Real.log 64 ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have herror : (64 * E) ^ 4 ≤ Real.log j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  exact ⟨fun d hd => modelCompetitorFactor_small hd hgeo,
    fun N hN hwindow => complete_middle_first_error_small hE hN hlog hwindow herror⟩

theorem exists_exponential_error_threshold {E c : ℝ} (hE : 0 < E) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ j : ℕ, T ≤ Real.log j →
      E * Real.exp (-c * (j : ℝ)) ≤ 1 / 64 := by
  let T : ℝ := max 1 (Real.log (64 * E) / c)
  refine ⟨T, (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _), ?_⟩
  intro j hjT
  have hjlog : 1 ≤ Real.log j := (le_max_left _ _).trans hjT
  have hj : 0 < j := by
    by_contra hh
    have hz : j = 0 := by omega
    norm_num [hz] at hjlog
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hquot : Real.log (64 * E) / c ≤ (j : ℝ) := by
    have hh := (le_max_right _ _).trans hjT
    have hl := Real.log_le_sub_one_of_pos hj0
    linarith
  have hmul := (div_le_iff₀ hc).mp hquot
  rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hE.ne'] at hmul
  calc
    _ = Real.exp (Real.log E - c * (j : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hE, neg_mul, Real.exp_neg]
      ring
    _ ≤ Real.exp (-Real.log 64) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 64)]; norm_num

end
end IsingBulk.AnisoF002.NegativeHT
