import IsingBulk.HT22.Far.ConstantBudget
import IsingBulk.HT22.Tail.ShellScale

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22

theorem far_shell_envelope_absorption {A C D M μ r ε : ℝ}
    (hA : 0≤A) (_hC : 0≤C) (hD : 0≤D) (hr : 0<r) (hε : 0≤ε)
    (hTM : |μ|+r+ε≤M) (m L : ℕ) :
    farOrderEnvelope A L (m+3)*C*((m+3:ℕ):ℝ)*D^(m+1)*
      (r/Real.sqrt (|μ|+r+ε))^m ≤
    farOrderEnvelope (A*(max 1 C)*(max 1 D)*(max 1 (Real.sqrt M))) (L+1) (m+3) := by
  let N := m+3
  let Q := max 1 C*max 1 D*max 1 (Real.sqrt M)
  have hΔ0 : 0≤r/Real.sqrt (|μ|+r+ε) := by positivity
  have hΔ : r/Real.sqrt (|μ|+r+ε)≤max 1 (Real.sqrt M) :=
    ((shellCoordinateScale_le_sqrt μ hr hε).trans (Real.sqrt_le_sqrt hTM)).trans (le_max_right _ _)
  have hc : C≤(max 1 C)^N := (le_max_right _ _).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (le_max_left 1 C) (show 1≤N by omega))
  have hd : D^(m+1)≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hs : (r/Real.sqrt (|μ|+r+ε))^m≤(max 1 (Real.sqrt M))^N :=
    (pow_le_pow_left₀ hΔ0 hΔ _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hcoef : C*D^(m+1)*(r/Real.sqrt (|μ|+r+ε))^m≤Q^N := by
    dsimp only [Q]
    rw [mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul hc hd (by positivity) (by positivity)) hs (by positivity) (by positivity)
  have he : 0≤farOrderEnvelope A L N := by unfold farOrderEnvelope shellOrderEnvelope;positivity
  calc
    _ = (farOrderEnvelope A L N*(N:ℝ))*(C*D^(m+1)*(r/Real.sqrt (|μ|+r+ε))^m) := by dsimp only [N];ring
    _ ≤ (farOrderEnvelope A L N*(N:ℝ))*Q^N := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = _ := by
      unfold farOrderEnvelope shellOrderEnvelope
      dsimp only [Q,N]
      rw [pow_succ]
      simp only [mul_div_assoc,mul_pow]
      ring

end
end IsingBulk.HT22.Far
