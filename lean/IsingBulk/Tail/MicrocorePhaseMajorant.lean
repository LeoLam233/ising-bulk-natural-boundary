import IsingBulk.Tail.MicrocoreFrozenAllOrder
import IsingBulk.Tail.MicrocoreVandermondeBound

/-! The unchanged full phase factor costs the Vandermonde degree and
exactly one simple sum kernel. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

theorem microcore_phase_factor_norm_bound {N : ℕ} (φ : Fin N → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hφ : ∀ i, ‖φ i‖ ≤ R) (hS : 0 < ∑ i, ‖φ i‖)
    (hZ : (∑ i, ‖φ i‖)/4 ≤ ‖1-Complex.exp (-Complex.I*∑ i, φ i)‖) :
    ‖microcorePhaseFactor φ‖ ≤ 4*(2*R)^(N*(N-1))/(∑ i, ‖φ i‖) := by
  unfold microcorePhaseFactor
  rw [norm_div]
  calc
    _ ≤ (2*R)^(N*(N-1))/((∑ i, ‖φ i‖)/4) :=
      div_le_div₀ (by positivity) (microcore_vandermonde_norm_bound φ hR hφ)
        (by positivity) hZ
    _ = _ := by ring

theorem microcore_integral_prefactor (E C K : ℝ) (hE : 0 < E) (hC : 0 < C) (hK : 0 < K) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N →
      8*Real.exp (E*(N:ℝ)^2)*(2*C)^(N*(N-1))*K^N ≤ Real.exp (D*(N:ℝ)^2) := by
  let L := 8+2*C+K
  have hL : 1 < L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  let D := E+3*Real.log L
  have hD : 0 < D := by
    have hh := Real.log_pos hL
    dsimp [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro N hN
  have hN2 : 1 ≤ N^2 := by nlinarith
  have hNle : N ≤ N^2 := by nlinarith
  have hdeg : N*(N-1) ≤ N^2 := by nlinarith [Nat.sub_le N 1]
  have h8 : 8 ≤ L^(N^2) := by
    have hl8 : 8 ≤ L := by dsimp [L]; linarith
    exact hl8.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL.le hN2)
  have hCpow : (2*C)^(N*(N-1)) ≤ L^(N^2) := by
    exact (pow_le_pow_left₀ (by positivity) (by dsimp [L]; linarith) _).trans
      (pow_le_pow_right₀ hL.le hdeg)
  have hKpow : K^N ≤ L^(N^2) :=
    (pow_le_pow_left₀ hK.le (by dsimp [L]; linarith) _).trans (pow_le_pow_right₀ hL.le hNle)
  calc
    _ ≤ L^(N^2)*Real.exp (E*(N:ℝ)^2)*L^(N^2)*L^(N^2) := by gcongr
    _ = Real.exp (E*(N:ℝ)^2)*L^(3*N^2) := by
      rw [show 3*N^2=N^2+N^2+N^2 by omega,pow_add,pow_add]
      ring
    _ = Real.exp (D*(N:ℝ)^2) := by
      rw [← Real.exp_log hL0,← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      dsimp [D]
      push_cast
      ring

end
end IsingBulk.Tail
