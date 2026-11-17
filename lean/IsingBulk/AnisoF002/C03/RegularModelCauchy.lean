import IsingBulk.AnisoF002.C03.RegularModelAnalyticFactors
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic
import IsingBulk.AnisoF002.C03.NegativeTaylorRemainder

/-!
# Finite differences of actual analytic inverse-particle corrections

Cauchy estimates are applied to the analytic functions on genuine complex
disks centered at the particle variable.  A filled x^2 factor produces
the required n^-3 first-difference and n^-4 second-difference scales.
No derivative is taken of asymptotic notation.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem analytic_first_taylor_remainder {s : Set ℂ} (hs : Convex ℝ s)
    {f : ℂ → ℂ} {c : ℂ} {M : ℝ} (hf : AnalyticOnNhd ℂ f s)
    (hc : c ∈ s) (hM : 0 ≤ M)
    (hsecond : ∀ y ∈ s, ‖deriv (deriv f) y‖ ≤ M) :
    ∀ x ∈ s, ‖f x - f c - deriv f c * (x - c)‖ ≤ M * ‖x - c‖ ^ 2 := by
  let R₁ : ℂ → ℂ := fun x => deriv f x - deriv f c
  let R₀ : ℂ → ℂ := fun x => f x - f c - deriv f c * (x - c)
  have hR₁ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₁ (deriv (deriv f) x) x :=
    (hf x hx).deriv.differentiableAt.hasDerivAt.sub_const _
  have hR₀ (x : ℂ) (hx : x ∈ s) : HasDerivAt R₀ (R₁ x) x := by
    have hl : HasDerivAt (fun y : ℂ => deriv f c * (y - c)) (deriv f c) x := by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_const_mul (deriv f c)).scomp x ((hasDerivAt_id' x).sub_const c)
    exact ((hf x hx).differentiableAt.hasDerivAt.sub_const _).sub hl
  have hb : ∀ x ∈ s, ‖R₁ x‖ ≤ M * ‖x - c‖ ^ 1 :=
    scalar_power_bound_of_derivative (k := 0) hs hc hM (by simp [R₁]) hR₁
      (fun x hx => by simpa only [pow_zero, mul_one] using hsecond x hx)
  exact scalar_power_bound_of_derivative (k := 1) hs hc hM (by simp) hR₀ hb

theorem analytic_centered_differences {f : ℂ → ℂ} {c δ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hb : ∀ z ∈ Metric.closedBall c r, ‖f z‖ ≤ M) (hδ : ‖δ‖ ≤ r / 2) :
    ‖f (c + δ) - f (c - δ)‖ ≤ 4 * M * ‖δ‖ / r ∧
      ‖f (c + δ) - 2 * f c + f (c - δ)‖ ≤ 16 * M * ‖δ‖ ^ 2 / r ^ 2 := by
  let K : Set ℂ := Metric.closedBall c (r / 2)
  have hsub : K ⊆ Metric.closedBall c r :=
    Metric.closedBall_subset_closedBall (half_le_self hr.le)
  have hfa : AnalyticOnNhd ℂ f K := hf.mono hsub
  have hc : c ∈ K := Metric.mem_closedBall_self (half_pos hr).le
  have hp : c + δ ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hδ
  have hm : c - δ ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hδ
  have hd (z : ℂ) (hz : z ∈ K) : ‖deriv f z‖ ≤ M / (r / 2) := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
      common_disk_iteratedDeriv_bound hr hf hb hz 1
  have hdd (z : ℂ) (hz : z ∈ K) : ‖deriv (deriv f) z‖ ≤ 2 * M / (r / 2) ^ 2 := by
    simpa [iteratedDeriv_succ] using
      common_disk_iteratedDeriv_bound hr hf hb hz 2
  constructor
  · have hh := (convex_closedBall c (r / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hfa z hz).differentiableAt) hd hm hp
    have he : c + δ - (c - δ) = 2 * δ := by ring
    rw [he, norm_mul] at hh
    norm_num only [Complex.norm_ofNat] at hh
    convert hh using 1
    ring
  · have hR := analytic_first_taylor_remainder (convex_closedBall c (r / 2)) hfa hc
      (by positivity : 0 ≤ 2 * M / (r / 2) ^ 2) hdd
    have hpR := hR (c + δ) hp
    have hmR := hR (c - δ) hm
    simp only [add_sub_cancel_left] at hpR
    simp only [sub_sub_cancel_left, norm_neg] at hmR
    have he : f (c + δ) - 2 * f c + f (c - δ) =
        (f (c + δ) - f c - deriv f c * δ) +
          (f (c - δ) - f c - deriv f c * (-δ)) := by ring
    rw [he]
    calc
      _ ≤ ‖f (c + δ) - f c - deriv f c * δ‖ +
          ‖f (c - δ) - f c - deriv f c * (-δ)‖ := norm_add_le _ _
      _ ≤ 2 * M / (r / 2) ^ 2 * ‖δ‖ ^ 2 + 2 * M / (r / 2) ^ 2 * ‖δ‖ ^ 2 :=
        add_le_add hpR hmR
      _ = _ := by ring

theorem exists_analytic_model_disk {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ AnalyticOnNhd ℂ U (Metric.closedBall 0 r) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖U z‖ ≤ M := by
  let M := ‖U 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hm : ∀ᶠ z in 𝓝 (0 : ℂ), ‖U z‖ < M :=
    hU.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp (hU.eventually_analyticAt.and hm)
  have hnear (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)) :
      AnalyticAt ℂ U z ∧ ‖U z‖ < M := hall
    ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  exact ⟨r / 2, M, half_pos hr, hM, fun z hz => (hnear z hz).1,
    fun z hz => (hnear z hz).2.le⟩

def inversePowerComposite (U : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ := z⁻¹ ^ k * U z⁻¹

theorem inversePowerComposite_disk {U : ℂ → ℂ} {r M n : ℝ} (k : ℕ)
    (hU : AnalyticOnNhd ℂ U (Metric.closedBall 0 r))
    (hb : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖U z‖ ≤ M)
    (hn : 0 < n) (hnr : 2 / n ≤ r) :
    AnalyticOnNhd ℂ (inversePowerComposite U k) (Metric.closedBall (n : ℂ) (n / 2)) ∧
      ∀ z ∈ Metric.closedBall (n : ℂ) (n / 2),
        ‖inversePowerComposite U k z‖ ≤ (2 / n) ^ k * M := by
  have hnorm (z : ℂ) (hz : z ∈ Metric.closedBall (n : ℂ) (n / 2)) : n / 2 ≤ ‖z‖ := by
    have hh := norm_sub_norm_le (n : ℂ) z
    rw [Complex.norm_real, Real.norm_of_nonneg hn.le, norm_sub_rev] at hh
    have hd : ‖z - (n : ℂ)‖ ≤ n / 2 := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    linarith
  have hinv (z : ℂ) (hz : z ∈ Metric.closedBall (n : ℂ) (n / 2)) : ‖z⁻¹‖ ≤ 2 / n := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (half_pos hn) (hnorm z hz)
    simpa only [one_div, inv_div] using hh
  have hzi (z : ℂ) (hz : z ∈ Metric.closedBall (n : ℂ) (n / 2)) :
      z⁻¹ ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hinv z hz).trans hnr
  constructor
  · intro z hz
    have hzn : z ≠ 0 := norm_pos_iff.mp ((half_pos hn).trans_le (hnorm z hz))
    have ha : AnalyticAt ℂ (fun z : ℂ => z⁻¹) z := analyticAt_id.inv hzn
    exact (ha.pow k).mul ((hU _ (hzi z hz)).comp ha)
  · intro z hz
    rw [inversePowerComposite, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hinv z hz) k) (hb _ (hzi z hz))
      (norm_nonneg _) (pow_nonneg (div_pos (by norm_num) hn).le k)

theorem inversePowerComposite_differences {U : ℂ → ℂ} {r M n d : ℝ} (k : ℕ)
    (hU : AnalyticOnNhd ℂ U (Metric.closedBall 0 r))
    (hb : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖U z‖ ≤ M)
    (hM : 0 ≤ M) (hn : 0 < n) (hnr : 2 / n ≤ r) (hd : 0 ≤ d) (hdn : d ≤ n / 4) :
    ‖inversePowerComposite U k ((n : ℂ) + d) - inversePowerComposite U k ((n : ℂ) - d)‖ ≤
        8 * (2 / n) ^ k * M * d / n ∧
      ‖inversePowerComposite U k ((n : ℂ) + d) - 2 * inversePowerComposite U k n +
        inversePowerComposite U k ((n : ℂ) - d)‖ ≤ 64 * (2 / n) ^ k * M * d ^ 2 / n ^ 2 := by
  obtain ⟨ha, hbound⟩ := inversePowerComposite_disk k hU hb hn hnr
  have hδ : ‖(d : ℂ)‖ ≤ (n / 2) / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hd]
    convert hdn using 1
    ring
  have hh := analytic_centered_differences (half_pos hn) (by positivity) ha hbound hδ
  simp only [Complex.norm_real, Real.norm_of_nonneg hd] at hh
  constructor
  · calc
      _ ≤ 4 * ((2 / n) ^ k * M) * d / (n / 2) := hh.1
      _ = _ := by ring
  · calc
      _ ≤ 16 * ((2 / n) ^ k * M) * d ^ 2 / (n / 2) ^ 2 := hh.2
      _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
