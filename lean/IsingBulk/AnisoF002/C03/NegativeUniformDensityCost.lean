import IsingBulk.AnisoF002.C03.NegativeScalarLogAssembly

/-!
# Particle-uniform conversion of the complete logarithmic cost

The winding angle pi/n, the actual quadratic pole displacement, all
pair multiplicities and the derivative-denominator error are combined
into the frozen sqrt(n Q) + n Q envelope.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

def densityLogBoundConstant (K A D C : ℝ) : ℝ :=
  K * C + 4 * K + 5 * K * A * (C + 1) + K * D * (C + 1) + 5 * K * A * Real.pi + 1

theorem densityLogBoundConstant_pos {K A D C : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    0 < densityLogBoundConstant K A D C := by
  unfold densityLogBoundConstant
  positivity

theorem complete_density_cost_uniform {N Q U d E e l K A D C : ℝ}
    (hN : 1 ≤ N) (hQ : 0 ≤ Q) (hU : 0 ≤ U) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hpole : N * U ≤ C * Q) (hangle : N * d ≤ Real.pi)
    (hphase : E ≤ A * (N * U + d * Real.sqrt (N * Q) + Q))
    (hden : e ≤ D * (U + Q / N))
    (hcost : l ≤ N ^ 2 * K * U + K * E + 4 * K * N * (Q + E) + K * e) :
    l ≤ densityLogBoundConstant K A D C * (Real.sqrt (N * Q) + N * Q) := by
  have hN0 : 0 < N := by linarith
  have hR : 0 ≤ Real.sqrt (N * Q) := Real.sqrt_nonneg _
  have hNQ : 0 ≤ N * Q := mul_nonneg hN0.le hQ
  have hNE : E ≤ N * E := by nlinarith
  have hNU : U ≤ N * U := by nlinarith
  have hQdiv : Q / N ≤ Q := (div_le_iff₀ hN0).mpr (by nlinarith)
  have hphaseN : N * E ≤ A * ((C + 1) * (N * Q) + Real.pi * Real.sqrt (N * Q)) := by
    calc
      N * E ≤ N * (A * (N * U + d * Real.sqrt (N * Q) + Q)) :=
        mul_le_mul_of_nonneg_left hphase hN0.le
      _ = A * (N * (N * U) + (N * d) * Real.sqrt (N * Q) + N * Q) := by ring
      _ ≤ A * (N * (C * Q) + Real.pi * Real.sqrt (N * Q) + N * Q) := by gcongr
      _ = _ := by ring
  have hden' : e ≤ D * (C + 1) * (N * Q) := by
    calc
      e ≤ D * (U + Q / N) := hden
      _ ≤ D * (C * Q + Q) := by gcongr; exact hNU.trans hpole
      _ = D * (C + 1) * Q := by ring
      _ ≤ D * (C + 1) * (N * Q) := by gcongr; nlinarith
  have hpower : N ^ 2 * K * U ≤ K * C * (N * Q) := by
    have hh := mul_le_mul_of_nonneg_left hpole (mul_nonneg hK hN0.le)
    nlinarith
  have hterms : K * E + 4 * K * N * E ≤ 5 * K * (N * E) := by
    have hh := mul_le_mul_of_nonneg_left hNE hK
    nlinarith
  let P : ℝ := K * C + 4 * K + 5 * K * A * (C + 1) + K * D * (C + 1)
  let S : ℝ := 5 * K * A * Real.pi
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hb : l ≤ P * (N * Q) + S * Real.sqrt (N * Q) := by
    have hd' := mul_le_mul_of_nonneg_left hden' hK
    have he' := mul_le_mul_of_nonneg_left hphaseN (by positivity : 0 ≤ 5 * K)
    dsimp [P, S]
    nlinarith
  have hP' : P ≤ P + S + 1 := by linarith
  have hS' : S ≤ P + S + 1 := by linarith
  calc
    l ≤ P * (N * Q) + S * Real.sqrt (N * Q) := hb
    _ ≤ (P + S + 1) * (N * Q) + (P + S + 1) * Real.sqrt (N * Q) := by gcongr
    _ = densityLogBoundConstant K A D C * (Real.sqrt (N * Q) + N * Q) := by
      unfold densityLogBoundConstant
      dsimp [P, S]
      ring

end
end IsingBulk.AnisoF002.NegativeHT
