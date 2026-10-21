import IsingBulk.HT.Tail.NegativeMicrocoreFactors
import IsingBulk.Tail.MicrocorePhaseMajorant
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail
open scoped BigOperators
theorem negative_microcore_phase_factor_norm_bound {N : ℕ} (φ : Fin N → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hφ : ∀ i, ‖φ i‖ ≤ R) (hS : 0 < ∑ i, ‖φ i‖)
    (hZ : (∑ i, ‖φ i‖)/4 ≤ ‖1+Complex.exp (-Complex.I*∑ i, φ i)‖) :
    ‖negativeMicrocorePhaseFactor φ‖ ≤ 4*(2*R)^(N*(N-1))/(∑ i, ‖φ i‖) := by
  unfold negativeMicrocorePhaseFactor
  rw [norm_div]
  calc
    _ ≤ (2*R)^(N*(N-1))/((∑ i, ‖φ i‖)/4) :=
      div_le_div₀ (by positivity) (microcore_vandermonde_norm_bound φ hR hφ)
        (by positivity) hZ
    _ = _ := by ring


end
end IsingBulk.HT.Tail
