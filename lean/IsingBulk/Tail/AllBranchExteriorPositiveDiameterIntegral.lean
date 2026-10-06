import IsingBulk.Tail.AllBranchExteriorPositiveCover

/-! Positive near-diagonal kernel bound for the complete branch-measure product.
The loss at a colliding extreme pair is paid by one diameter power. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem allBranchExterior_positive_diameter_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R α β : ℝ) (P : ℕ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    IntegrableOn (fun u => allBranchExteriorDiameter u^(P+1)*allBranchExteriorPositiveKernel d ε α β u)
      (@allBranchExteriorPositiveDiameterRegion N R a D) ∧
    (∫ u in @allBranchExteriorPositiveDiameterRegion N R a D,
      allBranchExteriorDiameter u^(P+1)*allBranchExteriorPositiveKernel d ε α β u) ≤
      (N:ℝ)^2*((D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2))) := by
  classical
  let S := @allBranchExteriorPositiveDiameterRegion N R a D
  let K := @allBranchExteriorPositiveKernel N d ε α β
  let f := fun u => allBranchExteriorDiameter u^(P+1)*K u
  let E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun pq => pq.1 ≠ pq.2)
  let cell := fun pq : Fin N × Fin N => allBranchExteriorPositiveGapCell pq.1 pq.2 R a D
  let g := fun (pq : Fin N × Fin N) u => (u pq.2-u pq.1)^(P+1)*K u
  let G := fun pq : Fin N × Fin N => (cell pq).indicator (g pq)
  let C := (D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2))
  have hS : MeasurableSet S := allBranchExterior_positive_diameter_region_measurable R a D
  have hcell (pq : Fin N × Fin N) : MeasurableSet (cell pq) :=
    allBranchExterior_positive_gap_cell_measurable pq.1 pq.2 R a D
  have hK (u : Fin N → ℝ) : 0 ≤ K u := allBranchExterior_positive_kernel_nonneg d ε α β u
  have hf0 (u : Fin N → ℝ) : 0 ≤ f u :=
    mul_nonneg (pow_nonneg (allBranchExterior_diameter_nonneg u) _) (hK u)
  have hG0 (pq : Fin N × Fin N) (u : Fin N → ℝ) : 0 ≤ G pq u := by
    apply indicator_nonneg
    intro v hv
    exact mul_nonneg (pow_nonneg hv.2.1.le _) (hK v)
  have hf : IntegrableOn f S := by
    have hc := ((@allBranchExterior_diameter_continuous N).pow (P+1)).continuousOn.mul
      (allBranchExterior_positive_kernel_continuousOn B hε hεr hR hRB hα hβ)
    exact hc.integrableOn_compact isCompact_Icc |>.mono_set (fun _ hu => hu.1)
  have hpairs (pq : Fin N × Fin N) (hpq : pq ∈ E) :
      IntegrableOn (g pq) (cell pq) ∧ (∫ u in cell pq, g pq u) ≤ C :=
    allBranchExterior_positive_power_product_integral B ε a D R α β P pq.1 pq.2
      (Finset.mem_filter.mp hpq).2 hε hεr ha hD hsmall₁ hsmall₂ hR hRB hRπ hα hα1 hβ hβ1
  have hGi (pq : Fin N × Fin N) (hpq : pq ∈ E) : Integrable (G pq) :=
    (integrable_indicator_iff (hcell pq)).mpr (hpairs pq hpq).1
  have hsum : Integrable (fun u => ∑ pq ∈ E, G pq u) := integrable_finsetSum E hGi
  have hpoint (u : Fin N → ℝ) : S.indicator f u ≤ ∑ pq ∈ E, G pq u := by
    by_cases hu : u ∈ S
    · obtain ⟨p,q,hpq,hmem,he⟩ := allBranchExterior_positive_diameter_region_cover hu
      have hE : (p,q) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpq⟩
      have hone := Finset.single_le_sum (fun pq (_ : pq ∈ E) => hG0 pq u) hE
      rw [indicator_of_mem hu]
      have heq : G (p,q) u=f u := by
        rw [show G (p,q) u=(cell (p,q)).indicator (g (p,q)) u from rfl,indicator_of_mem hmem]
        change (u q-u p)^(P+1)*K u=allBranchExteriorDiameter u^(P+1)*K u
        rw [he]
      rwa [heq] at hone
    · rw [indicator_of_notMem hu]
      exact Finset.sum_nonneg (fun pq _ => hG0 pq u)
  have hC : 0 ≤ C := by
    have hcost := allBranchExterior_positive_cost_nonneg B ha hD
    have hsc := simpleKernelConstant_pos
    have hlength := B.lengthC_pos
    dsimp [C]
    positivity
  have hcard : (E.card:ℝ) ≤ (N:ℝ)^2 := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun pq : Fin N × Fin N => pq.1 ≠ pq.2) Finset.univ)
    have hh' : E.card ≤ N*N := by simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using hh
    exact_mod_cast (show E.card ≤ N^2 by simpa only [pow_two] using hh')
  refine ⟨hf,?_⟩
  change (∫ u in S, f u) ≤ (N:ℝ)^2*C
  calc
    _ = ∫ u, S.indicator f u := (integral_indicator hS).symm
    _ ≤ ∫ u, ∑ pq ∈ E, G pq u :=
      integral_mono ((integrable_indicator_iff hS).mpr hf) hsum hpoint
    _ = ∑ pq ∈ E, ∫ u, G pq u := integral_finsetSum E hGi
    _ ≤ ∑ _pq ∈ E, C := by
      apply Finset.sum_le_sum
      intro pq hpq
      change (∫ u, (cell pq).indicator (g pq) u) ≤ C
      rw [integral_indicator (hcell pq)]
      exact (hpairs pq hpq).2
    _ = (E.card:ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

end
end IsingBulk.Tail
