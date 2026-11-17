import IsingBulk.AnisoF002.C03.IsotropicPeriodicDistance

/-!
# The frozen oblique product-kernel majorant

The distance is the exact distance to the winding lattice. Radial
attenuation and the exponential chord estimate give a bound valid
for every phase and every positive lower attenuation, including large
attenuation. The projection is exactly the frozen 3 pi / 8 rotation.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

def dampedExponential (a x : ℝ) : ℂ :=
  Complex.exp ((-a : ℝ) - Complex.I * (x : ℂ))

theorem dampedExponential_norm (a x : ℝ) : ‖dampedExponential a x‖ = Real.exp (-a) := by
  rw [dampedExponential, Complex.norm_exp]
  simp

theorem dampedExponential_split (a x : ℝ) :
    dampedExponential a x = (Real.exp (-a) : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) := by
  rw [dampedExponential, sub_eq_add_neg, Complex.exp_add, ← Complex.ofReal_exp]
  congr 2
  ring

theorem radial_exponential_loss (a : ℝ) (ha : a ∈ Icc 0 1) :
    a / 2 ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith only [ha.1]
  have hle : Real.exp (-a) ≤ 1 / (1 + a) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos (by linarith only [Real.add_one_le_exp a])
  have he : 1 - 1 / (1 + a) = a / (1 + a) := by field_simp; ring
  have hrat : a / 2 ≤ a / (1 + a) := by
    apply (div_le_div_iff₀ (by norm_num) hpos).mpr
    nlinarith only [ha.1, ha.2]
  linarith only [hle, he, hrat]

theorem damped_exponential_radial_lower (a x : ℝ) :
    1 - Real.exp (-a) ≤ ‖1 - dampedExponential a x‖ := by
  have hh := norm_sub_norm_le (1 : ℂ) (dampedExponential a x)
  simpa only [norm_one, dampedExponential_norm] using hh

theorem damped_exponential_chord_control (a x : ℝ) (ha : 0 ≤ a) :
    ‖1 - Complex.exp (-Complex.I * (x : ℂ))‖ ≤ 2 * ‖1 - dampedExponential a x‖ := by
  have hr : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hnorm : ‖dampedExponential a x - Complex.exp (-Complex.I * (x : ℂ))‖ = 1 - Real.exp (-a) := by
    rw [dampedExponential_split,
      show (Real.exp (-a) : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) - Complex.exp (-Complex.I * (x : ℂ)) =
        ((Real.exp (-a) : ℂ) - 1) * Complex.exp (-Complex.I * (x : ℂ)) by ring,
      norm_mul, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, neg_zero,
      Real.exp_zero, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hr)]
    ring
  have ht := norm_add_le (1 - dampedExponential a x)
    (dampedExponential a x - Complex.exp (-Complex.I * (x : ℂ)))
  rw [sub_add_sub_cancel, hnorm] at ht
  have hl := damped_exponential_radial_lower a x
  linarith only [ht, hl]

theorem frozen_oblique_periodic_distance (a x : ℝ) (ha : 0 ≤ a) :
    periodicDistance (2 * Real.pi * Real.cos frozenObliqueAngle)
      (frozenObliqueRotation * ((x : ℂ) - Complex.I * (a : ℂ))).re ≤
        periodicDistance (2 * Real.pi) x + a := by
  have he : (frozenObliqueRotation * ((x : ℂ) - Complex.I * (a : ℂ))).re =
      Real.cos frozenObliqueAngle * x - Real.sin frozenObliqueAngle * a := by
    rw [frozenObliqueRotation_eq]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
      zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub]
    ring
  rw [he]
  have hh := periodicDistance_sub_le (2 * Real.pi * Real.cos frozenObliqueAngle)
    (Real.cos frozenObliqueAngle * x) (Real.sin frozenObliqueAngle * a)
  rw [show 2 * Real.pi * Real.cos frozenObliqueAngle = Real.cos frozenObliqueAngle * (2 * Real.pi) by ring,
    periodicDistance_scaled, abs_of_pos frozenObliqueAngle_cos_pos, abs_mul, abs_of_nonneg ha] at hh
  have hcos := mul_le_mul_of_nonneg_right (Real.cos_le_one frozenObliqueAngle)
    (periodicDistance_nonneg (2 * Real.pi) x)
  have hsin := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one frozenObliqueAngle) ha
  rw [show 2 * Real.pi * Real.cos frozenObliqueAngle = Real.cos frozenObliqueAngle * (2 * Real.pi) by ring]
  nlinarith only [hh, hcos, hsin]

/-- Frozen `eq:iso-oblique-kernel`, with the distance represented by its
exact additive-circle norm and explicitly identified with `infDist` to
the winding lattice in `periodicDistance_eq_infDist`. -/
theorem frozen_oblique_kernel_bound (a₀ a x : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1) (ha : a₀ ≤ a) :
    1 / ‖1 - Complex.exp (-Complex.I * ((x : ℂ) - Complex.I * (a : ℂ)))‖ ≤
      (4 + 2 * Real.pi) /
        (a₀ + periodicDistance (2 * Real.pi * Real.cos frozenObliqueAngle)
          (frozenObliqueRotation * ((x : ℂ) - Complex.I * (a : ℂ))).re) := by
  have hap : 0 < a := ha₀.trans_le ha
  let D := ‖1 - dampedExponential a x‖
  let d := periodicDistance (2 * Real.pi * Real.cos frozenObliqueAngle)
    (frozenObliqueRotation * ((x : ℂ) - Complex.I * (a : ℂ))).re
  have hD : 0 < D := by
    have he : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hap)
    exact (sub_pos.mpr he).trans_le (damped_exponential_radial_lower a x)
  have hd : 0 ≤ d := periodicDistance_nonneg _ _
  have hmajor : a₀ + d ≤ (4 + 2 * Real.pi) * D := by
    by_cases ha1 : a ≤ 1
    · have hr := radial_exponential_loss a ⟨hap.le, ha1⟩
      have hrad := damped_exponential_radial_lower a x
      have hchord := damped_exponential_chord_control a x hap.le
      have hang := periodicDistance_exp_chord x
      have hoblique := frozen_oblique_periodic_distance a x hap.le
      have hπD := mul_nonneg Real.pi_pos.le hD.le
      change d ≤ _ at hoblique
      change _ ≤ D at hrad
      change _ ≤ 2 * D at hchord
      have hchord' := mul_le_mul_of_nonneg_left hchord (half_pos Real.pi_pos).le
      nlinarith only [ha, hr, hrad, hchord', hang, hoblique, hπD]
    · have ha1' : 1 ≤ a := (lt_of_not_ge ha1).le
      have he : Real.exp (-a) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith only [ha1'])
      have hr := radial_exponential_loss 1 ⟨by norm_num, le_rfl⟩
      have hrad := damped_exponential_radial_lower a x
      have hhalf : 1 / 2 ≤ D := by change _ ≤ D at hrad; linarith only [he, hr, hrad]
      have hp : 0 < 2 * Real.pi * Real.cos frozenObliqueAngle :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) frozenObliqueAngle_cos_pos
      have hdhalf := periodicDistance_le_half (2 * Real.pi * Real.cos frozenObliqueAngle)
        (frozenObliqueRotation * ((x : ℂ) - Complex.I * (a : ℂ))).re hp
      change d ≤ _ at hdhalf
      have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one frozenObliqueAngle) Real.pi_pos.le
      have hbound : a₀ + d ≤ 1 + Real.pi := by nlinarith only [ha₀1, hdhalf, hc]
      have hm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4 + 2 * Real.pi by positivity)
      nlinarith only [hbound, hm]
  have he : -Complex.I * ((x : ℂ) - Complex.I * (a : ℂ)) = (-a : ℝ) - Complex.I * (x : ℂ) := by
    push_cast
    linear_combination (a : ℂ) * Complex.I_sq
  rw [he]
  change 1 / D ≤ (4 + 2 * Real.pi) / (a₀ + d)
  exact (div_le_div_iff₀ hD (by linarith only [ha₀, hd])).mpr (by simpa only [one_mul] using hmajor)

end IsingBulk.AnisoF002.Isotropic
