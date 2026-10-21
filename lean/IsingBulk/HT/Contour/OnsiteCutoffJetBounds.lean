import IsingBulk.Tail.SectorCutoffJetBounds
import IsingBulk.HT.Contour.OnsiteLieSupport

/-! Dimension-uniform jets of the actual onsite real cutoff weights. The
outer-role is identically two, hence its factor is exactly one; there is no
outer-anchor partition or named-current scalar in these real jet bounds. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Tail IsingBulk.Jets
open scoped BigOperators ContDiff

theorem onsite_sectorScalarFamily_product {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (sigma role : Fin N → Fin 3) (u : Fin N → ℝ) :
    (∏ i,sectorScalarFamily f b inner inner hi hi ((2:Fin 3),sigma i,role i) (u i))=
      sectorAssignmentWeight b inner hi sigma u*∏ i,selectorSectorScalar f (role i) (u i) := by
  simp only [sectorScalarFamily,outerSectorScalar,
    show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide,ite_false,one_mul,
    Finset.prod_mul_distrib,sectorAssignmentWeight]

/-- Fixed-order constants precede the dimension, assignment, current index
and every word. Both weights are the literal real products used by onsite
Lie transport; the scalar -2*i*tau remains outside the named weight. -/
theorem onsite_sector_cutoff_jet_bounds (f : SelectorFunctions) (hf : RegularSelector f)
    (b inner : ℝ) (hi : 0< inner) (order : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∀ sigma : Fin N → Fin 3,
      ∀ l : List (Fin N),l.length≤order → ∀ θ : Fin N → ℝ,
        ‖cutoffJet l (fun x => angularSelector f x*sectorAssignmentWeight b inner hi sigma x) θ‖≤C^N ∧
        ∀ q : Fin N,
          ‖cutoffJet l (fun x => namedSelectorDerivative f q x*sectorAssignmentWeight b inner hi sigma x) θ‖≤C^N := by
  let g := sectorScalarFamily f b inner inner hi hi
  obtain ⟨C,hC,hbound⟩ := finite_periodic_factor_product_jets g
    (fun label => (sectorScalarFamily_regular f hf b inner inner hi hi label).1)
    (fun label => (sectorScalarFamily_regular f hf b inner inner hi hi label).2) order
  refine ⟨C,hC,?_⟩
  intro N sigma l hl θ
  have hsel : (fun x : Fin N → ℝ => ∏ i,g ((2:Fin 3),sigma i,(1:Fin 3)) (x i))=
      (fun x => angularSelector f x*sectorAssignmentWeight b inner hi sigma x) := by
    funext x
    rw [onsite_sectorScalarFamily_product,selectorSectorScalar_original_product,mul_comm]
  have hcur (q : Fin N) : (fun x : Fin N → ℝ =>
      ∏ i,g ((2:Fin 3),sigma i,if i=q then (2:Fin 3) else 1) (x i))=
      (fun x => namedSelectorDerivative f q x*sectorAssignmentWeight b inner hi sigma x) := by
    funext x
    rw [onsite_sectorScalarFamily_product,selectorSectorScalar_current_product,mul_comm]
  constructor
  · rw [← hsel]
    exact hbound N (fun i => ((2:Fin 3),sigma i,(1:Fin 3))) l hl θ
  · intro q
    rw [← hcur q]
    exact hbound N (fun i => ((2:Fin 3),sigma i,if i=q then (2:Fin 3) else 1)) l hl θ

end
end IsingBulk.HT.Contour
