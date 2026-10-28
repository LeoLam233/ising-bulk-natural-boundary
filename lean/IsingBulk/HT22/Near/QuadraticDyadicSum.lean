import IsingBulk.HT22.Near.DyadicSum
import IsingBulk.HT22.Tail.ExponentArithmetic

namespace IsingBulk.HT22.Near
noncomputable section
open scoped BigOperators

theorem near_quadratic_dyadic_sum (μ : ℝ) {ε δ C : ℝ} (hε : 0≤ε)
    (hδ : 0<δ) (hδ1 : δ≤1) (hC : 0≤C) (hsmall : C*δ≤1/2)
    {j k p N : ℕ} (hjk : j≤k) (hp : 1≤p)
    (hdegree : (p:ℝ)=(N:ℝ)^2-2*(j:ℝ)-3) :
    Summable (fun n => C^(N^2)*(if dyadicScale μ ε n≤δ then dyadicScale μ ε n^p else 0)) ∧
      (∑' n,C^(N^2)*(if dyadicScale μ ε n≤δ then dyadicScale μ ε n^p else 0))≤
        4*δ^(-2*(k:ℝ)-3)*nearOrderEnvelope N := by
  obtain ⟨hs,hb⟩ := dyadic_near_power_sum μ hε hδ.le hp
  have hnum := near_shell_threshold_bound hC hδ hδ1 hsmall hjk N
  rw [←hdegree,Real.rpow_natCast] at hnum
  refine ⟨hs.mul_left _,?_⟩
  rw [tsum_mul_left]
  calc
    _ ≤ C^(N^2)*(4*δ^p) := mul_le_mul_of_nonneg_left hb (pow_nonneg hC _)
    _ = 4*(C^(N^2)*δ^p) := by ring
    _ ≤ 4*(δ^(-2*(k:ℝ)-3)*nearOrderEnvelope N) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    _ = _ := by ring

end
end IsingBulk.HT22.Near
