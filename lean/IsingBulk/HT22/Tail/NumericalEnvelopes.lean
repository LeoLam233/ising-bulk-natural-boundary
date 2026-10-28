import IsingBulk.Preferred22.AbsoluteTail

/-! # F001 near/far all-odd-order numerical envelopes

The far-envelope theorem reused below is a generic real-series estimate,
not the LT coefficient tail.  This file proves only numerical summation;
no angular coefficient estimate is included among its assumptions or conclusions.
-/
namespace IsingBulk.HT22
noncomputable section
open Filter
open scoped Topology BigOperators

/-- The near-shell envelope in F001 §8 after the fixed threshold is chosen. -/
def nearOrderEnvelope (N : ℕ) : ℝ := (1/2 : ℝ)^(N^2)

/-- The far-shell envelope, including a fixed polynomial cost. -/
def farOrderEnvelope (C : ℝ) (J N : ℕ) : ℝ :=
  IsingBulk.Preferred22.shellOrderEnvelope C J N

theorem nearOrderEnvelope_nonneg (N : ℕ) : 0 ≤ nearOrderEnvelope N := by
  unfold nearOrderEnvelope
  positivity

theorem nearOrderEnvelope_le_geometric (N : ℕ) :
    nearOrderEnvelope N ≤ (1/2 : ℝ)^N := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith

theorem nearOrderEnvelope_summable : Summable nearOrderEnvelope :=
  (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).of_nonneg_of_le
      nearOrderEnvelope_nonneg nearOrderEnvelope_le_geometric

theorem farOrderEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C) (J N : ℕ) :
    0 ≤ farOrderEnvelope C J N := by
  unfold farOrderEnvelope IsingBulk.Preferred22.shellOrderEnvelope
  positivity

theorem farOrderEnvelope_summable {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (farOrderEnvelope C J) :=
  IsingBulk.Preferred22.shell_order_envelope_summable hC J

theorem farOrderEnvelope_eq_rpow (C : ℝ) (J N : ℕ) (hN : 0 < N) :
    farOrderEnvelope C J N = C^N*(N:ℝ)^(-(N:ℝ)/2+(J:ℝ)) :=
  IsingBulk.Preferred22.shell_order_envelope_eq_rpow C J N hN

/-- All positive odd orders are retained, starting with one, not three. -/
theorem oddOrder_injective : Function.Injective (fun n : ℕ => 2*n+1) := by
  intro a b h
  change 2*a+1=2*b+1 at h
  omega

theorem odd_nearOrderEnvelope_summable :
    Summable (fun n : ℕ => nearOrderEnvelope (2*n+1)) :=
  nearOrderEnvelope_summable.comp_injective oddOrder_injective

theorem odd_farOrderEnvelope_summable {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (fun n : ℕ => farOrderEnvelope C J (2*n+1)) :=
  (farOrderEnvelope_summable hC J).comp_injective oddOrder_injective

/-- A single N-independent envelope contains both parts of the geometric split. -/
def completeOrderEnvelope (A C : ℝ) (J N : ℕ) : ℝ :=
  A*nearOrderEnvelope N+farOrderEnvelope C J N

theorem completeOrderEnvelope_nonneg {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (J N : ℕ) : 0 ≤ completeOrderEnvelope A C J N :=
  add_nonneg (mul_nonneg hA (nearOrderEnvelope_nonneg N)) (farOrderEnvelope_nonneg hC J N)

theorem completeOrderEnvelope_summable (A : ℝ) {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (completeOrderEnvelope A C J) :=
  (nearOrderEnvelope_summable.mul_left A).add (farOrderEnvelope_summable hC J)

theorem odd_completeOrderEnvelope_summable (A : ℝ) {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (fun n : ℕ => completeOrderEnvelope A C J (2*n+1)) :=
  (completeOrderEnvelope_summable A hC J).comp_injective oddOrder_injective

/-- A generic absolute-series adapter. Its pointwise hypothesis is deliberately
visible: applying it to the physical coefficients still requires the full F001
transport, shell integration, and sector decomposition proofs. -/
theorem odd_absolute_sum_bound {A C H : ℝ} (hC : 0 ≤ C)
    (J : ℕ) (f : ℕ → ℂ)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ completeOrderEnvelope A C J (2*n+1)*H) :
    Summable (fun n => ‖f n‖) ∧
      (∑' n, ‖f n‖) ≤ (∑' n, completeOrderEnvelope A C J (2*n+1))*H := by
  have he := (odd_completeOrderEnvelope_summable A hC J).mul_right H
  have hf := he.of_nonneg_of_le (fun n => norm_nonneg (f n)) hbound
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' n, completeOrderEnvelope A C J (2*n+1)*H := hf.tsum_le_tsum hbound he
    _ = _ := tsum_mul_right

/-- The F001 logarithmic envelope is lower order than the actual odd first
singularity epsilon^(-1), rather than the LT epsilon^(-1/2) scale. -/
theorem logarithmic_factor_times_parameter_tendsto_zero :
    Tendsto (fun eps : ℝ => eps*(1+|Real.log eps|)) (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun eps : ℝ => eps) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun eps : ℝ => Real.log eps*eps) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 1)
  have hh := hi.add hl.abs
  simp only [abs_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hpos : 0 < eps := heps
  rw [abs_mul, abs_of_pos hpos]
  ring

end
end IsingBulk.HT22
