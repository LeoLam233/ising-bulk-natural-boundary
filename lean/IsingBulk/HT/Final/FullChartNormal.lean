import IsingBulk.HT.Final.LeftFullSeries
import IsingBulk.HT.Final.RightFullSeries

/-! Full-site local normal majorants are formed from the separately proved
onsite and offsite majorants on each genuine source chart. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set Filter Metric
open scoped Topology BigOperators

private theorem norm_full_bound (a b : ℂ) {u v : ℝ} (ha : ‖a‖ ≤ u) (hb : ‖b‖ ≤ v) :
    ‖a+2*b‖ ≤ u+2*v := by
  have hn := norm_add_le a (2*b)
  simp only [norm_mul,Complex.norm_ofNat] at hn
  linarith

theorem upperFull_local_normal {s : ℂ} (hs : 0 < (sourceS s).im) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ upperTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖upperFullCoefficient (2*n+1) t‖ ≤ u n := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := upperOnsiteOdd_local_normal hs
  obtain ⟨V,hV,hsV,_hsubV,v,hv,hc⟩ := upperOdd_local_normal hs
  exact ⟨U ∩ V,hU.inter hV,⟨hsU,hsV⟩,inter_subset_left.trans hsub,
    fun n => u n+2*v n,hu.add (hv.mul_left 2),
    fun n t ht => norm_full_bound _ _ (hb n t ht.1) (hc n t ht.2)⟩

theorem rightFull_local_normal {s : ℂ} (hs : 2 < (sourceS s).re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ rightTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖rightFullCoefficient (2*n+1) t‖ ≤ u n := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := rightOnsiteOdd_local_normal hs
  obtain ⟨V,hV,hsV,_hsubV,v,hv,hc⟩ := rightOdd_local_normal hs
  exact ⟨U ∩ V,hU.inter hV,⟨hsU,hsV⟩,inter_subset_left.trans hsub,
    fun n => u n+2*v n,hu.add (hv.mul_left 2),
    fun n t ht => norm_full_bound _ _ (hb n t ht.1) (hc n t ht.2)⟩

theorem leftFull_local_normal {s : ℂ} (hs : (sourceS s).re < -2) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ leftTraceDomain ∧
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n t, t ∈ U → ‖leftFullCoefficient (2*n+1) t‖ ≤ u n := by
  obtain ⟨U,hU,hsU,hsub,u,hu,hb⟩ := leftOnsiteOdd_local_normal hs
  obtain ⟨V,hV,hsV,_hsubV,v,hv,hc⟩ := leftOdd_local_normal hs
  exact ⟨U ∩ V,hU.inter hV,⟨hsU,hsV⟩,inter_subset_left.trans hsub,
    fun n => u n+2*v n,hu.add (hv.mul_left 2),
    fun n t ht => norm_full_bound _ _ (hb n t ht.1) (hc n t ht.2)⟩

end
end IsingBulk.HT.Final
