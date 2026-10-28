import IsingBulk.First.SmoothCutoffConstruction

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff

/-- Ordered smooth partition, allowing overlapping source charts without
assuming disjoint supports or a bound on fiber component counts. -/
def chartPartition {ι E : Type*} (χ : ι → E → ℝ) : List ι → List (E → ℝ)
  | [] => []
  | i::L => χ i :: (chartPartition χ L).map (fun ψ x => (1-χ i x)*ψ x)

def chartRemainder {ι E : Type*} (χ : ι → E → ℝ) (L : List ι) (x : E) : ℝ :=
  (L.map (fun i => 1-χ i x)).prod

theorem chartPartition_identity {ι E : Type*} (χ : ι → E → ℝ) (L : List ι) (x : E) :
    ((chartPartition χ L).map (fun ψ => ψ x)).sum+chartRemainder χ L x=1 := by
  induction L with
  | nil => simp [chartPartition,chartRemainder]
  | cons i L ih =>
    simp only [chartPartition,List.map_cons,List.sum_cons,List.map_map,chartRemainder,List.prod_cons]
    have he : ((chartPartition χ L).map (fun ψ => (1-χ i x)*ψ x)).sum=
        (1-χ i x)*((chartPartition χ L).map (fun ψ => ψ x)).sum := by
      induction chartPartition χ L with
      | nil => simp
      | cons ψ P ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]
    simp only [Function.comp_def]
    rw [he]
    dsimp only [chartRemainder] at ih
    linear_combination (1-χ i x)*ih

theorem chartRemainder_zero {ι E : Type*} (χ : ι → E → ℝ) (L : List ι)
    {i : ι} (hi : i∈L) {x : E} (hx : χ i x=1) : chartRemainder χ L x=0 := by
  unfold chartRemainder
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨i,hi,by simp [hx]⟩

theorem chartPartition_support {ι E : Type*} (χ : ι → E → ℝ) (L : List ι)
    {ψ : E → ℝ} (hψ : ψ∈chartPartition χ L) :
    ∃ i∈L, Function.support ψ ⊆ Function.support (χ i) := by
  induction L generalizing ψ with
  | nil => simp [chartPartition] at hψ
  | cons i L ih =>
    simp only [chartPartition,List.mem_cons,List.mem_map] at hψ
    rcases hψ with rfl | ⟨φ,hφ,rfl⟩
    · exact ⟨i,by simp,Subset.rfl⟩
    · obtain ⟨j,hj,hs⟩ := ih hφ
      refine ⟨j,List.mem_cons_of_mem _ hj,?_⟩
      intro x hx
      apply hs
      exact (mul_ne_zero_iff.mp hx).2

theorem chartPartition_contDiff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : ι → E → ℝ) (L : List ι) (hχ : ∀ i∈L,ContDiff ℝ ∞ (χ i)) :
    ∀ ψ∈chartPartition χ L,ContDiff ℝ ∞ ψ := by
  induction L with
  | nil => simp [chartPartition]
  | cons i L ih =>
    intro ψ hψ
    simp only [chartPartition,List.mem_cons,List.mem_map] at hψ
    rcases hψ with rfl | ⟨φ,hφ,rfl⟩
    · exact hχ i (by simp)
    · exact (contDiff_const.sub (hχ i (by simp))).mul
        (ih (fun j hj => hχ j (List.mem_cons_of_mem _ hj)) φ hφ)

theorem chartRemainder_contDiff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : ι → E → ℝ) (L : List ι) (hχ : ∀ i∈L,ContDiff ℝ ∞ (χ i)) :
    ContDiff ℝ ∞ (chartRemainder χ L) := by
  induction L with
  | nil => exact contDiff_const
  | cons i L ih =>
    change ContDiff ℝ ∞ (fun x => (1-χ i x)*chartRemainder χ L x)
    exact (contDiff_const.sub (hχ i (by simp))).mul
      (ih (fun j hj => hχ j (List.mem_cons_of_mem _ hj)))

theorem chartRemainder_eq_zero_near {ι E : Type*} [TopologicalSpace E]
    (χ : ι → E → ℝ) (L : List ι) {i : ι} (hi : i∈L) {x : E}
    (hx : χ i =ᶠ[𝓝 x] fun _ => 1) : chartRemainder χ L =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hx] with y hy
  exact chartRemainder_zero χ L hi hy

end
end IsingBulk.HT22.Geometry
