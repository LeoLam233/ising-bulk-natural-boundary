import IsingBulk.HT22.FullTail.PartitionBound
namespace IsingBulk.HT22.FullTail
noncomputable section
open scoped BigOperators

/-- Pure nonnegative-series assembly; applications below discharge all three
component bounds using the actual physical constructions. -/
theorem absolute_sum_of_components (C F R A : ℕ → ℝ)
    (hC : ∀ n,0≤C n) (hF : Summable F) (hR : Summable R) (hA : Summable A)
    (hbound : ∀ n,C n≤F n+2*(R n+A n))
    {HF HR HA : ℝ} (hbF : (∑' n,F n)≤HF) (hbR : (∑' n,R n)≤HR)
    (hbA : (∑' n,A n)≤HA) :
    Summable C ∧ (∑' n,C n)≤HF+2*(HR+HA) := by
  have hs : Summable (fun n => F n+2*(R n+A n)) := hF.add ((hR.add hA).mul_left 2)
  have hc := hs.of_nonneg_of_le hC hbound
  refine ⟨hc,(hc.tsum_le_tsum hbound hs).trans ?_⟩
  rw [hF.tsum_add ((hR.add hA).mul_left 2),tsum_mul_left,hR.tsum_add hA]
  linarith

end
end IsingBulk.HT22.FullTail
