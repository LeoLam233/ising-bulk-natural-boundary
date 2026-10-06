import IsingBulk.Final.RadialNoncancellation
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The absolute sum in thm:tail really controls the complex higher-order
series; pointwise little-o of individual particle orders would not suffice. -/
namespace IsingBulk.Final
noncomputable section
open Filter
open scoped Topology

theorem complex_tail_isLittleO_of_absolute {ι : Type*} {T : ℝ → ι → ℂ}
    (hs : ∀ᶠ e : ℝ in 𝓝[>] 0, Summable (fun i => ‖T e i‖))
    (ht : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => ∑' i, ‖T e i‖) (fun e => (Real.sqrt e)⁻¹)) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => ∑' i, T e i) (fun e => (Real.sqrt e:ℂ)⁻¹) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [hs,ht.bound hc] with e he hbound
  have hnonneg : 0 ≤ ∑' i, ‖T e i‖ := tsum_nonneg (fun _ => norm_nonneg _)
  calc
    ‖∑' i, T e i‖ ≤ ∑' i, ‖T e i‖ := norm_tsum_le_tsum_norm he
    _ = ‖∑' i, ‖T e i‖‖ := (Real.norm_of_nonneg hnonneg).symm
    _ ≤ c * ‖(Real.sqrt e)⁻¹‖ := hbound
    _ = c * ‖(Real.sqrt e:ℂ)⁻¹‖ := by simp only [norm_inv,Complex.norm_real]

end
end IsingBulk.Final
