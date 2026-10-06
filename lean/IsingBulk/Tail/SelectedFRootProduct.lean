import IsingBulk.Tail.SelectedFActualPairs
import IsingBulk.Tail.IndexedPairProductBound

/-! The actual selected root-pair product has compact-count Gaussian decay.
Every indexed pair is retained, including collisions; no pair product is
canceled by division in the estimate. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology BigOperators

 theorem pairProduct_indexed_norm {N : ℕ} (z : Fin N → ℂ) :
    ‖First.pairProduct z‖ = ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
      ‖pairKernel (z p.1) (z p.2)‖ := by
  simp only [First.pairProduct,norm_prod,orderedIndexPairs,Finset.prod_filter,Finset.prod_product,apply_ite,norm_one]

 theorem actual_pairProduct_two_group_bound {N : ℕ} (hN : 0 < N)
    (J : Finset (Fin N)) (color : Fin N → Bool) (z : Fin N → ℂ)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hsame : ∀ i ∈ J, ∀ j ∈ J, color i=color j → ‖pairKernel (z i) (z j)‖ ≤ q)
    (hall : ∀ i j, ‖pairKernel (z i) (z j)‖ ≤ 1+C/(N:ℝ)) :
    ‖First.pairProduct z‖ ≤ Real.exp ((C-Real.log q/2)*(N:ℝ))*
      Real.exp ((Real.log q/4)*(J.card:ℝ)^2) := by
  let g : Fin N → Fin 2 := fun i => finTwoEquiv.symm (color i)
  rw [pairProduct_indexed_norm]
  apply indexed_two_group_product_bound hN J g (fun p => ‖pairKernel (z p.1) (z p.2)‖)
    hC hq hq1 (fun _ _ => norm_nonneg _) (fun p _ => hall p.1 p.2)
  intro p hp
  simp only [sameColorPairs,orderedIndexPairs,Finset.mem_filter,Finset.mem_product] at hp
  exact hsame p.1 hp.1.1.1 p.2 hp.1.1.2 (finTwoEquiv.symm.injective hp.2)

 theorem selected_actual_root_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ B a : ℝ, 0 < c ∧ 0 < eps₀ ∧ 0 < B ∧ 0 < a ∧
        ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → θ ∈ angleBox N →
          θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ) →
          ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
          ‖First.pairProduct (fun i => selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ i))‖ ≤
            B^N*Real.exp (-a*((selectedCompactIndexSet d.thetaB η θ).card:ℝ)^2) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hpairs⟩ := selected_actual_pair_bounds d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨c,eps₀,C,q,hc,heps₀,hC,hq,hq1,hb⟩ := hpairs η α τ hη hηlt hα hαsmall hτ hτlt
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  refine ⟨c,eps₀,Real.exp (C-Real.log q/2),-Real.log q/4,hc,heps₀,Real.exp_pos _,by linarith,?_⟩
  intro N eps θ s hN heps hepslt hθ hsupport hsd
  obtain ⟨color,hsame,hall⟩ := hb N eps θ s hN heps hepslt hθ hsupport hsd
  have hh := actual_pairProduct_two_group_bound (by omega : 0<N)
    (selectedCompactIndexSet d.thetaB η θ) color _ hC.le hq hq1 hsame hall
  have he : (Real.exp (C-Real.log q/2))^N=Real.exp ((C-Real.log q/2)*(N:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simpa only [neg_div,neg_neg] using hh

end
end IsingBulk.Tail
