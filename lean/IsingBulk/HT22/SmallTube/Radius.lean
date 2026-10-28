import IsingBulk.HT22.SmallTube.Mask
import IsingBulk.HT22.Geometry.SignedShellUpperScale
namespace IsingBulk.HT22.SmallTube
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators

theorem sqrt_radius_power_le {R : ℝ} (hR : 0 ≤ R) (hRπ : R ≤ Real.pi)
    {q : ℕ} (hq : 6 ≤ q) :
    (Real.sqrt R)^q ≤ R^3 * (max 1 (Real.sqrt Real.pi))^q := by
  let M := max 1 (Real.sqrt Real.pi)
  have hM : 1 ≤ M := le_max_left _ _
  have hrM : Real.sqrt R ≤ M := (Real.sqrt_le_sqrt hRπ).trans (le_max_right _ _)
  have hsix : (Real.sqrt R)^6 = R^3 := by
    rw [show 6=2*3 from rfl, pow_mul, Real.sq_sqrt hR]
  calc
    (Real.sqrt R)^q = (Real.sqrt R)^6 * (Real.sqrt R)^(q-6) := by rw [←pow_add, Nat.add_sub_of_le hq]
    _ ≤ R^3 * M^(q-6) := by rw [hsix]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg R) hrM _) (by positivity)
    _ ≤ R^3 * M^q := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.sub_le _ _)) (by positivity)

theorem dyadic_radius_cube (m : ℕ) :
    (preferredDyadicRadius m)^3 = Real.pi^3 * (1/8:ℝ)^m := by
  unfold preferredDyadicRadius
  rw [pow_succ (1/2:ℝ) m]
  have h : 2*Real.pi*((1/2:ℝ)^m*(1/2)) = Real.pi*(1/2:ℝ)^m := by ring
  rw [h,mul_pow,←pow_mul, Nat.mul_comm m 3,pow_mul]
  norm_num

theorem dyadic_sqrt_power_le {q : ℕ} (hq : 6 ≤ q) (m : ℕ) :
    (Real.sqrt (preferredDyadicRadius m))^q ≤
      (Real.pi^3 * (max 1 (Real.sqrt Real.pi))^q) * (1/8:ℝ)^m := by
  calc
    _ ≤ (preferredDyadicRadius m)^3 * (max 1 (Real.sqrt Real.pi))^q :=
      sqrt_radius_power_le (preferredDyadicRadius_pos m).le (preferredDyadicRadius_le_pi m) hq
    _ = _ := by rw [dyadic_radius_cube]; ring
end
end IsingBulk.HT22.SmallTube
