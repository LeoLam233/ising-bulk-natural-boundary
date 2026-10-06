import IsingBulk.First.ContourNormBounds
import IsingBulk.First.SmallRadiusDensityBounds

/-! An actual geometric form-factor bound at a fixed small contour radius.
It is used only in a neighborhood of infinity. -/
namespace IsingBulk.First
noncomputable section

theorem doubleFormFactor_quarter_norm_bound_of_dispersion (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hD : ∀ x ∈ productCircle N (1/4), ∀ y ∈ productCircle N (1/4), ∀ i,
      1 ≤ ‖dispersion (x i) (y i) s‖) :
    ‖doubleFormFactor N (1/4) s‖ ≤ 8*(1/4:ℝ)^N := by
  have h := doubleFormFactor_norm_le N (r := 1/4) (by norm_num) s (C := 8*(4:ℝ)^N)
    (fun x hx y hy => doubleDensity_quarter_norm_bound_of_dispersion hN s x y hx hy (hD x hx y hy))
  have hfacpos : (0:ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hfac : (N.factorial:ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hfacpos).mpr
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos N))
  have hp : (1/4:ℝ)^N*((1/4:ℝ)^N*(8*(4:ℝ)^N)) = 8*(1/4:ℝ)^N := by
    calc
      _ = 8*(1/4:ℝ)^N*(((1/4:ℝ)*4)^N) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  rw [hp] at h
  exact h.trans (by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/4) N])

end
end IsingBulk.First
