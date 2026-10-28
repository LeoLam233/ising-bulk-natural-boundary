import IsingBulk.HT22.Geometry.FiniteCenterCutoffs

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

/-- A prescribed critical chart is placed first and its cutoff is never
multiplied by another partition factor. Every remaining local piece is
assigned to a different center. -/
theorem finite_center_partition_with_first {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Finset ι) (i₀ : ι) (center : ι → E) (R : ι → ℝ) (R₀ : ℝ)
    (hR₀ : 0<R₀) (hR : ∀ i∈S.erase i₀,0<R i) :
    ∃ χ₀ : E → ℝ,∃ P : List (E → ℝ),∃ rem : E → ℝ,∃ ρ : ℝ,0<ρ ∧
      ContDiff ℝ ∞ χ₀ ∧ HasCompactSupport χ₀ ∧ (∀ x,0≤χ₀ x ∧ χ₀ x≤1) ∧
      tsupport χ₀⊆ball (center i₀) R₀ ∧ χ₀ =ᶠ[𝓝 (center i₀)] (fun _ => 1) ∧
      ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        ∃ i∈S.erase i₀,tsupport ψ⊆ball (center i) (R i)) ∧
      (∀ x,χ₀ x+(P.map (fun ψ => ψ x)).sum+rem x=1) ∧
      (∀ i∈S,∀ x,‖x-center i‖≤ρ → rem x=0) ∧
      (∀ i∈S,∀ x,‖x-center i‖<ρ → rem =ᶠ[𝓝 x] (fun _ => 0)) := by
  classical
  let R' : ι → ℝ := fun i => if i=i₀ then R₀ else R i
  have hR' (i : ι) (hi : i∈insert i₀ S) : 0<R' i := by
    by_cases he : i=i₀
    · simpa only [R',ite_eq_left he] using hR₀
    · have hiS : i∈S := (Finset.mem_insert.mp hi).resolve_left he
      simpa only [R',ite_eq_right he] using hR i (Finset.mem_erase.mpr ⟨he,hiS⟩)
  obtain ⟨χ,ρ,hρ,hχ,hunit⟩ := exists_finite_center_cutoffs (insert i₀ S) center R' hR'
  let L := (S.erase i₀).toList
  let P := (chartPartition χ L).map (fun ψ x => (1-χ i₀ x)*ψ x)
  have hcrit := hχ i₀ (Finset.mem_insert_self ..)
  have hL (i : ι) : i∈L ↔ i∈S.erase i₀ := Finset.mem_toList
  have hmem (i : ι) (hi : i∈S) : i∈i₀::L := by
    by_cases he : i=i₀
    · simp [he]
    · exact List.mem_cons_of_mem _ ((hL i).mpr (Finset.mem_erase.mpr ⟨he,hi⟩))
  have hc (i : ι) (hi : i∈i₀::L) : ContDiff ℝ ∞ (χ i) := by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hcrit.1
    · exact (hχ i (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase ((hL i).mp hi)))).1
  refine ⟨χ i₀,P,chartRemainder χ (i₀::L),ρ,hρ,hcrit.1,hcrit.2.1,hcrit.2.2.1,?_,?_,
    chartRemainder_contDiff χ (i₀::L) hc,?_,?_,?_,?_⟩
  · simpa only [R',ite_eq_left (rfl : i₀=i₀)] using hcrit.2.2.2
  · filter_upwards [ball_mem_nhds (center i₀) hρ] with x hx
    apply hunit i₀ (Finset.mem_insert_self ..) x
    exact (by simpa only [mem_ball,dist_eq_norm] using hx : ‖x-center i₀‖<ρ).le
  · intro ψ hψ
    obtain ⟨φ,hφ,rfl⟩ := List.mem_map.mp hψ
    obtain ⟨i,hi,hs⟩ := chartPartition_support χ L hφ
    have hiS := (hL i).mp hi
    have hi' : i∈insert i₀ S := Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hiS)
    have hci := hχ i hi'
    have ht : tsupport (fun x => (1-χ i₀ x)*φ x)⊆tsupport (χ i) :=
      tsupport_mul_subset_right.trans (closure_mono hs)
    refine ⟨(contDiff_const.sub hcrit.1).mul
      (chartPartition_contDiff χ L (fun j hj => hc j (List.mem_cons_of_mem _ hj)) φ hφ),
      hci.2.1.of_isClosed_subset (isClosed_tsupport _) ht,i,hiS,?_⟩
    have hh := ht.trans hci.2.2.2
    simpa only [R',ite_eq_right (Finset.mem_erase.mp hiS).1] using hh
  · intro x
    simpa only [chartPartition,List.map_cons,List.sum_cons,P] using chartPartition_identity χ (i₀::L) x
  · intro i hi x hx
    exact chartRemainder_zero χ (i₀::L) (hmem i hi)
      (hunit i (Finset.mem_insert_of_mem hi) x hx)
  · intro i hi x hx
    have hev : ∀ᶠ y in 𝓝 x,y∈ball (center i) ρ :=
      isOpen_ball.mem_nhds (show x∈ball (center i) ρ by simpa only [mem_ball,dist_eq_norm] using hx)
    filter_upwards [hev] with y hy
    have hy' : ‖y-center i‖<ρ := by simpa only [mem_ball,dist_eq_norm] using hy
    exact chartRemainder_zero χ (i₀::L) (hmem i hi)
      (hunit i (Finset.mem_insert_of_mem hi) y hy'.le)


end
end IsingBulk.HT22.Geometry
