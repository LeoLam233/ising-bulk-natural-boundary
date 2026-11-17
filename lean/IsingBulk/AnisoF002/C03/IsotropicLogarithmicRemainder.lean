import IsingBulk.AnisoF002.C03.IsotropicFirstSmoothAttachment
import IsingBulk.AnisoF002.C03.IsotropicCollisionFiniteComplement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Every proved logarithmic remainder vanishes at the actual first scale

The radial scaling is epsilon=s². The complete logarithmic bounds are
therefore negligible after multiplication by either first singular power,
and more generally by any positive integer power of s.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology

theorem isotropic_power_log_square_tendsto_zero {l : ℕ} (hl : 0 < l) :
    Tendsto (fun s : ℝ => s ^ l * (1 + |Real.log (s ^ 2)|)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow : Tendsto (fun s : ℝ => s ^ l) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_pow hl.ne'] using hid.pow l
  have hlog : Tendsto (fun s : ℝ => Real.log s * s ^ l) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_log_mul_rpow_nhdsGT_zero (show 0 < (l : ℝ) by exact_mod_cast hl)
  have habs := hlog.abs
  have ht : Tendsto (fun s : ℝ => s ^ l + 2 * |Real.log s * s ^ l|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero, mul_zero, add_zero] using hpow.add (tendsto_const_nhds.mul habs)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Real.log_pow]
  simp only [Nat.cast_ofNat, abs_mul, abs_pow, abs_of_pos (show (0 : ℝ) < s from hs)]
  norm_num
  ring

theorem scaled_logarithmic_remainder_tendsto_zero {f : ℝ → ℂ} {A : ℝ} {l : ℕ}
    (hl : 0 < l)
    (hb : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ‖f s‖ ≤ A * (1 + |Real.log (s ^ 2)|)) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * f s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ => A * (s ^ l * (1 + |Real.log (s ^ 2)|)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (isotropic_power_log_square_tendsto_zero hl)
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin, hb] with s hs hb
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le l)).trans_eq (by ring)

theorem radial_logarithmic_remainder_scaled_zero {f : ℝ → ℂ} {A δ : ℝ} {l : ℕ}
    (hδ : 0 < δ) (hl : 0 < l)
    (hb : ∀ ε ∈ Ioo 0 δ, ‖f ε‖ ≤ A * (1 + |Real.log ε|)) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * f (s ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply scaled_logarithmic_remainder_tendsto_zero hl
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < δ :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hδ))).filter_mono
        nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsd
  exact hb (s ^ 2) ⟨sq_pos_of_pos hs, hsd⟩

end
end IsingBulk.AnisoF002.Isotropic
