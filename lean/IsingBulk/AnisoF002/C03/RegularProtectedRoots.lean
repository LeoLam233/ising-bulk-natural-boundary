import IsingBulk.AnisoF002.C03.RegularProtectedScale

/-!
# Uniform protected continuation of the complete finite reciprocal family

The radius is chosen before the particle number. Every original root is
continued with its prescribed sign, every pair denominator is retained,
and the full root product stays strictly inside the unit disk.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology BigOperators

def continuedRoots {N : ℕ} (W r : Fin N → ℂ) (z : ℂ) (i : Fin N) : ℂ :=
  reciprocalRootContinuation (W i) (r i) (W i + z)

theorem exists_uniform_reciprocal_root_disk (H κ c g : ℝ)
    (hH : 0 ≤ H) (hκ : 0 < κ) (hc : 0 < c) (hg : 0 < g) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ (N : ℕ), 0 < N → ∀ W r : Fin N → ℂ,
      (∀ i, r i ^ 2 - 2 * W i * r i + 1 = 0) →
      (∀ i, ‖W i‖ ≤ H) → (∀ i, κ ≤ ‖r i‖) → (∀ i, ‖r i‖ ≤ 1) →
      (∀ i j, c / N ≤ ‖1 - r i * r j‖) →
      (∀ i j, ‖schur (r i) (r j)‖ ≤ 1) →
      ‖∏ i, r i‖ ≤ 1 - g / N →
      ∀ z : ℂ, ‖z‖ ≤ ρ / (N : ℝ) ^ 6 →
      (∀ i, AnalyticAt ℂ (fun t => continuedRoots W r t i) z) ∧
      (∀ i, ‖continuedRoots W r z i‖ ≤ 2 * ‖r i‖) ∧
      (∀ i j, ‖1 - r i * r j‖ / 2 ≤
        ‖1 - continuedRoots W r z i * continuedRoots W r z j‖) ∧
      (∀ i j, ‖schur (continuedRoots W r z i) (continuedRoots W r z j)‖ ≤
        1 + 1 / (N : ℝ) ^ 2) ∧
      ‖∏ i, continuedRoots W r z i‖ ≤ 1 - g / (2 * N) := by
  let K := 1 + 2 * (2 * H + 1) / c
  have hK : 0 < K := by dsimp [K]; positivity
  let a := min κ (min (c / 10) (min 1 (g / (2 * Real.exp 1))))
  have ha : 0 < a := by dsimp [a]; positivity
  have haκ : a ≤ κ := min_le_left _ _
  have hac : a ≤ c / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have ha1 : a ≤ 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hag : a ≤ g / (2 * Real.exp 1) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let ρ := min 1 (min (c ^ 2 / (8 * (2 * H + 1))) (a / K))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρc : 8 * (2 * H + 1) * ρ ≤ c ^ 2 := by
    have hh : ρ ≤ c ^ 2 / (8 * (2 * H + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 8 * (2 * H + 1))).mp hh
    nlinarith
  have hρa : K * ρ ≤ a := by
    have hh : ρ ≤ a / K := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ hK).mp hh
    nlinarith
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro N hN W r hp hW hrlo hrhi hgap hschur hprod z hz
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz1 : ‖z‖ ≤ 1 := by
    have hh := power_scaled_norm_le hN hρ.le hz (k := 0) (by omega)
    simpa only [pow_zero, one_mul] using hh.trans hρ1
  let h := K * N * ‖z‖
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hN3 : (N : ℝ) ^ 3 * h ≤ a := by
    have hs := mul_le_mul_of_nonneg_left
      (power_scaled_norm_le hN hρ.le hz (k := 4) (by omega)) hK.le
    apply le_trans _ hρa
    convert hs using 1
    dsimp [h]
    ring
  have hN2 : (N : ℝ) ^ 2 * h ≤ a := by
    have hn : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by omega)
    exact (mul_le_mul_of_nonneg_right hn hh).trans hN3
  have hNmul : (N : ℝ) * h ≤ a := by
    have hn : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hN1 (show 1 ≤ 3 by omega)
    exact (mul_le_mul_of_nonneg_right hn hh).trans hN3
  have hha : h ≤ a := by
    have hn : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    have hm := mul_le_mul_of_nonneg_right hn hh
    simpa only [one_mul] using hm.trans hN3
  have hh1 : h ≤ 1 := hha.trans ha1
  have hv (i : Fin N) : ‖continuedRoots W r z i - r i‖ ≤ h := by
    apply reciprocalRootContinuation_uniform_variation (hp i) (hrhi i) hH (hW i) hc hN _ z hz1
    simpa only [pow_two] using hgap i i
  have hnew (i : Fin N) : ‖continuedRoots W r z i‖ ≤ 2 * ‖r i‖ := by
    have ht := norm_le_norm_sub_add (continuedRoots W r z i) (r i)
    have hb : h ≤ ‖r i‖ := (hha.trans haκ).trans (hrlo i)
    linarith [hv i]
  have hsmall : 6 * h ≤ c / N := by
    apply (le_div_iff₀ hN0).mpr
    have hb := hNmul.trans hac
    nlinarith
  have hhalf (i j : Fin N) : ‖1 - r i * r j‖ / 2 ≤
      ‖1 - continuedRoots W r z i * continuedRoots W r z j‖ :=
    root_pair_gap_half hh hh1 (hrhi i) (hrhi j) (hv i) (hv j) (hsmall.trans (hgap i j))
  have hq (i j : Fin N) :
      ‖schur (continuedRoots W r z i) (continuedRoots W r z j)‖ ≤ 1 + 1 / (N : ℝ) ^ 2 := by
    apply (schur_perturbed_norm_le hh hh1 (div_pos hc hN0) (hrhi i) (hrhi j)
      (hv i) (hv j) (hgap i j) hsmall (hschur i j)).trans
    apply add_le_add le_rfl
    apply (div_le_iff₀ (div_pos hc hN0)).mpr
    have hb := hN3.trans hac
    have he : (1 / (N : ℝ) ^ 2) * (c / N) = c / (N : ℝ) ^ 3 := by ring
    rw [he]
    apply (le_div_iff₀ (pow_pos hN0 3)).mpr
    nlinarith
  have hproddiff : ‖(∏ i, continuedRoots W r z i) - ∏ i, r i‖ ≤ Real.exp 1 * N * h := by
    have hb := finite_prod_perturbation r (continuedRoots W r z) hh hrhi hv
    have he := one_add_pow_le_exp_one hh N (hNmul.trans ha1)
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (N : ℝ) * h)
    apply hb.trans
    convert hm using 1
    ring
  have hproderr : Real.exp 1 * N * h ≤ g / (2 * N) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mpr
    have hb := hN2.trans hag
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * Real.exp 1)).mp hb
    nlinarith
  refine ⟨?_, hnew, hhalf, hq, ?_⟩
  · intro i
    apply reciprocalRootContinuation_analytic_on_protected_disk hN hH hc hρ.le hρ1 hρc
      (hp i) (hrhi i) (hW i) _ hz
    simpa only [pow_two] using hgap i i
  · have ht := norm_le_norm_sub_add (∏ i, continuedRoots W r z i) (∏ i, r i)
    have he : g / (N : ℝ) = 2 * (g / (2 * N)) := by ring
    linarith [hproddiff.trans hproderr]

end
end IsingBulk.AnisoF002.RegularTail.C03
