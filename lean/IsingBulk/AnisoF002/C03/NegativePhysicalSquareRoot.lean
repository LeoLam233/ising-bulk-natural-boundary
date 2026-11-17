import IsingBulk.AnisoF002.C03.NegativeUniformDensityLog
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Analytic square root with the prescribed physical center value

Normalization is by B(0), so the scalar square root is taken near 1.
Either prescribed center root is retained exactly.  The physical
normalization can therefore be attached without a branch change.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

def normalizedLocalSquareRoot (B : ℂ → ℂ) (b₀ : ℂ) (t : ℂ) : ℂ :=
  b₀ * Complex.sqrt (B t / B 0)

theorem normalizedLocalSquareRoot_center {B : ℂ → ℂ} (b₀ : ℂ) (hB : B 0 ≠ 0) :
    normalizedLocalSquareRoot B b₀ 0 = b₀ := by
  simp only [normalizedLocalSquareRoot, div_self hB, Complex.sqrt, Complex.one_cpow, mul_one]

theorem normalizedLocalSquareRoot_sq {B : ℂ → ℂ} {b₀ : ℂ}
    (hB : B 0 ≠ 0) (hb₀ : b₀ ^ 2 = B 0) (t : ℂ) :
    normalizedLocalSquareRoot B b₀ t ^ 2 = B t := by
  have hs : Complex.sqrt (B t / B 0) ^ 2 = B t / B 0 := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (B t / B 0) 2
  rw [normalizedLocalSquareRoot, mul_pow, hs, hb₀]
  exact mul_div_cancel₀ _ hB

theorem normalizedLocalSquareRoot_analyticAt {B : ℂ → ℂ} (b₀ : ℂ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0) :
    AnalyticAt ℂ (normalizedLocalSquareRoot B b₀) 0 := by
  have hslit : B 0 / B 0 ∈ Complex.slitPlane := by
    simpa only [div_self hB0] using Complex.one_mem_slitPlane
  have hs : AnalyticAt ℂ (fun t : ℂ => Complex.sqrt (B t / B 0)) 0 := by
    simpa only [Complex.sqrt] using hB.div_const.cpow
      (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hslit
  exact analyticAt_const.mul hs

theorem normalizedLocalSquareRoot_center_ne_zero {B : ℂ → ℂ} {b₀ : ℂ}
    (hB : B 0 ≠ 0) (hb₀ : b₀ ^ 2 = B 0) : normalizedLocalSquareRoot B b₀ 0 ≠ 0 := by
  rw [normalizedLocalSquareRoot_center b₀ hB]
  intro hzero
  rw [hzero, zero_pow (by decide)] at hb₀
  exact hB hb₀.symm

end
end IsingBulk.AnisoF002.NegativeHT
