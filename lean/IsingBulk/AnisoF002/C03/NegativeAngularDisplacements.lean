import IsingBulk.AnisoF002.C03.NegativeAngularPowerBounds
import IsingBulk.AnisoF002.C03.NegativePoleDensityBridge

/-! # The genuine constrained angular directions in the complex pole chart -/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open scoped BigOperators

def angularComplexDisplacement {d : ℕ} (r : ℝ) (θ : AngularSphere d) :
    zeroSumDisplacements (d + 1) :=
  ⟨fun i => ((r * (θ.val : Ambient d) i : ℝ) : ℂ), by
    change angleSum (d + 1) (fun i => ((r * (θ.val : Ambient d) i : ℝ) : ℂ)) = 0
    rw [angleSum_apply, ← Complex.ofReal_sum, ← Finset.mul_sum, constrained_sum,
      mul_zero, Complex.ofReal_zero]⟩

@[simp] theorem angularComplexDisplacement_apply {d : ℕ} (r : ℝ)
    (θ : AngularSphere d) (i : Fin (d + 1)) :
    (angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i =
      ((r * (θ.val : Ambient d) i : ℝ) : ℂ) := rfl

theorem continuous_angularComplexDisplacement (d : ℕ) (r : ℝ) :
    Continuous (angularComplexDisplacement (d := d) r) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) i).comp
      (continuous_subtype_val.comp continuous_subtype_val)))

theorem angularComplexDisplacement_square {d : ℕ} (r : ℝ) (θ : AngularSphere d) :
    displacementSquare (d + 1) (angularComplexDisplacement r θ) = r ^ 2 := by
  unfold displacementSquare
  simp only [angularComplexDisplacement_apply, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, mul_pow]
  rw [← Finset.mul_sum, angular_norm_sq, mul_one]

theorem angularComplexDisplacement_complex_square {d : ℕ} (r : ℝ) (θ : AngularSphere d) :
    (∑ i, (angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i ^ 2) = (r ^ 2 : ℝ) := by
  simp only [angularComplexDisplacement_apply, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
  congr 1
  simp only [mul_pow]
  rw [← Finset.mul_sum, angular_norm_sq, mul_one]

theorem angularComplexDisplacement_cubic {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (θ : AngularSphere d) :
    (∑ i, ‖(angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i‖ ^ 3) ≤
      r ^ 3 * Real.sqrt (angularZ θ) / Real.sqrt ((d + 1 : ℕ) : ℝ) := by
  simpa only [angularComplexDisplacement_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr] using angular_scaled_cubic_power_sum θ r

theorem angularComplexDisplacement_quartic {d : ℕ} (r : ℝ) (θ : AngularSphere d) :
    (∑ i, ‖(angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i‖ ^ 4) ≤
      r ^ 4 * angularZ θ / ((d + 1 : ℕ) : ℝ) := by
  simpa only [angularComplexDisplacement_apply, Complex.norm_real, Real.norm_eq_abs,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using angular_scaled_fourth_power_sum θ r

end
end IsingBulk.AnisoF002.NegativeHT.Angular
