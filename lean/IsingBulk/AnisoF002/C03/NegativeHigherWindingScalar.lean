import IsingBulk.AnisoF002.C03.NegativeWindingHighParticle
import IsingBulk.AnisoF002.C03.NegativeWindingModelMajorants

/-!
# Quantitative absorption of every higher winding

The finite sector count and all center/curvature costs are at most
exponential in N².  The exact factor (2/9)^(j+1-alpha) then dominates
them once j exceeds one fixed multiple of N².
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem higher_winding_scalar_envelope {K C σ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hσ : σ ≤ 1) {N α : ℕ} (hN : 1 ≤ N) (hα : α ≤ N ^ 2) :
    (2 * (N : ℝ) + 1) * K * (2 : ℝ) ^ (N ^ 2) * Real.exp (C * (N : ℝ) * σ) *
      (4 : ℝ) ^ α ≤ Real.exp ((K + C + 10) * (N : ℝ) ^ 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hαR : (α : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hα
  have hcount : 2 * (N : ℝ) + 1 ≤ Real.exp (3 * (N : ℝ) ^ 2) := by
    nlinarith [Real.add_one_le_exp (3 * (N : ℝ) ^ 2)]
  have hKe : K ≤ Real.exp ((K + 1) * (N : ℝ) ^ 2) := by
    calc
      _ ≤ Real.exp (K + 1) := by linarith [Real.add_one_le_exp (K + 1)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (2 : ℝ) ^ (N ^ 2) ≤ Real.exp (2 * (N : ℝ) ^ 2) := by
    calc
      _ ≤ (Real.exp 2) ^ (N ^ 2) := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : (4 : ℝ) ^ α ≤ Real.exp (4 * (N : ℝ) ^ 2) := by
    calc
      _ ≤ (Real.exp 4) ^ α := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) _
      _ = Real.exp (4 * (α : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hCe : Real.exp (C * (N : ℝ) * σ) ≤ Real.exp (C * (N : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ C * (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hσ (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hNsq hC
  calc
    _ ≤ Real.exp (3 * (N : ℝ) ^ 2) * Real.exp ((K + 1) * (N : ℝ) ^ 2) *
        Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (C * (N : ℝ) ^ 2) *
        Real.exp (4 * (N : ℝ) ^ 2) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem exists_higher_winding_scalar_window {D : ℝ} (hD : 0 < D) :
    ∃ M : ℝ, 1 < M ∧ ∀ N α m : ℕ, 1 ≤ N → α ≤ N ^ 2 →
      M * (N : ℝ) ^ 2 ≤ ((α + m : ℕ) : ℝ) →
      Real.exp (D * (N : ℝ) ^ 2) * (2 / 9 : ℝ) ^ (m + 1) ≤ 1 / 32 := by
  let L := Real.log (9 / 2)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hlog32 : 0 < Real.log (32 : ℝ) := Real.log_pos (by norm_num)
  let M := 1 + (D + Real.log 32 + 1) / L
  have hM : 1 < M := by
    have hp : 0 < (D + Real.log 32 + 1) / L := div_pos (by positivity) hL
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro N α m hN hα hw
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hαR : (α : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hα
  have hLM : L * M = L + D + Real.log 32 + 1 := by dsimp [M]; field_simp; ring
  have hwL := mul_le_mul_of_nonneg_left hw hL.le
  have hαL := mul_le_mul_of_nonneg_left hαR hL.le
  rw [← mul_assoc, hLM, Nat.cast_add] at hwL
  have hkey : D * (N : ℝ) ^ 2 - L * ((m + 1 : ℕ) : ℝ) ≤ -Real.log 32 := by
    push_cast
    nlinarith [mul_nonneg hlog32.le (sub_nonneg.mpr hNsq)]
  have hlog : Real.log (2 / 9 : ℝ) = -L := by
    rw [show (2 / 9 : ℝ) = (9 / 2)⁻¹ by norm_num, Real.log_inv]
  have hp : (2 / 9 : ℝ) ^ (m + 1) = Real.exp (-L * ((m + 1 : ℕ) : ℝ)) := by
    rw [show -L * ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * Real.log (2 / 9 : ℝ)
      by rw [hlog]; ring, Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (2 / 9 : ℝ))]
  rw [hp, ← Real.exp_add]
  calc
    _ ≤ Real.exp (-Real.log 32) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 32 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 32)]; norm_num

end
end IsingBulk.AnisoF002.NegativeHT
