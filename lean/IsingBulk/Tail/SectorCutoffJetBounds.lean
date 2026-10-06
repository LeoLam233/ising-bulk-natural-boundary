import IsingBulk.Tail.PeriodicFactorJets
import IsingBulk.Tail.NestedSectorPartition

/-! Dimension-uniform real jets of the actual nested partition multiplied
by the original selector or a named current cutoff. All scalar factors
are fixed smooth periodic functions before N is chosen. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped BigOperators ContDiff

def outerSectorScalar (b delta : ℝ) (hd : 0 < delta) (k : Fin 3) (x : ℝ) : ℝ :=
  if k=0 then sectorBranch b delta hd x else if k=1 then 1-sectorBranch b delta hd x else 1

def selectorSectorScalar (f : SelectorFunctions) (k : Fin 3) (x : ℝ) : ℝ :=
  if k=0 then 1 else if k=1 then 1-f.a x else -deriv f.a x

def sectorScalarFamily (f : SelectorFunctions) (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Fin 3 × Fin 3 × Fin 3) (x : ℝ) : ℝ :=
  outerSectorScalar b outer ho label.1 x * sectorLabel b inner hi label.2.1 x * selectorSectorScalar f label.2.2 x

theorem outerSectorScalar_smooth (b delta : ℝ) (hd : 0 < delta) (k : Fin 3) :
    ContDiff ℝ ∞ (outerSectorScalar b delta hd k) := by
  change ContDiff ℝ ∞ (fun x => outerSectorScalar b delta hd k x)
  by_cases h0 : k=0
  · simp only [outerSectorScalar,h0,ite_true]
    exact (sector_labels_smooth b delta hd).2.2
  · by_cases h1 : k=1
    · simp only [outerSectorScalar,h1,ite_true]
      exact contDiff_const.sub (sector_labels_smooth b delta hd).2.2
    · simp only [outerSectorScalar,h0,h1,ite_false]
      exact contDiff_const

theorem selectorSectorScalar_smooth (f : SelectorFunctions) (hf : RegularSelector f) (k : Fin 3) :
    ContDiff ℝ ∞ (selectorSectorScalar f k) := by
  change ContDiff ℝ ∞ (fun x => selectorSectorScalar f k x)
  by_cases h0 : k=0
  · simp only [selectorSectorScalar,h0,ite_true]
    exact contDiff_const
  · by_cases h1 : k=1
    · simp only [selectorSectorScalar,h1,ite_true]
      exact contDiff_const.sub hf.a_smooth
    · simp only [selectorSectorScalar,h0,h1,ite_false]
      have hd : ContDiff ℝ ∞ (deriv f.a) := by apply ContDiff.deriv'; simpa using hf.a_smooth
      exact hd.neg

theorem sectorScalarFamily_regular (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (label : Fin 3 × Fin 3 × Fin 3) :
    ContDiff ℝ ∞ (sectorScalarFamily f b outer inner ho hi label) ∧
      Function.Periodic (sectorScalarFamily f b outer inner ho hi label) (2*Real.pi) := by
  have hlabel : ContDiff ℝ ∞ (sectorLabel b inner hi label.2.1) := by
    rcases sector_labels_smooth b inner hi with ⟨hL,hR,hB⟩
    unfold sectorLabel
    split_ifs <;> assumption
  constructor
  · exact ((outerSectorScalar_smooth b outer ho label.1).mul hlabel).mul
      (selectorSectorScalar_smooth f hf label.2.2)
  · intro x
    have hB := (sector_labels_periodic b outer ho).2.2 x
    have hLi := (sector_labels_periodic b inner hi).1 x
    have hRi := (sector_labels_periodic b inner hi).2.1 x
    have hBi := (sector_labels_periodic b inner hi).2.2 x
    have ha := hf.a_periodic x
    have had := periodic_derivative hf.a_periodic x
    simp only [sectorScalarFamily,outerSectorScalar,sectorLabel,selectorSectorScalar,hB,hLi,hRi,hBi,ha,had]

theorem outerAnchor_coordinate_product {N : ℕ} (chi : ℝ → ℝ) (q : Fin N) (u : Fin N → ℝ) :
    outerAnchor (finiteExtension (fun i => chi (u i))) q =
      ∏ i : Fin N, if i<q then chi (u i) else if i=q then 1-chi (u i) else 1 := by
  have hprefix : (∏ i ∈ Finset.univ.filter (fun i : Fin N => i<q), chi (u i)) =
      ∏ k ∈ Finset.range q, finiteExtension (fun i => chi (u i)) k := by
    apply Finset.prod_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro k hk
      have hkq := Finset.mem_range.mp hk
      exact ⟨⟨k,hkq.trans q.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkq⟩,rfl⟩
    · intro i hi
      exact (finiteExtension_fin (fun i => chi (u i)) i).symm
  have hf (i : Fin N) : (if i<q then chi (u i) else if i=q then 1-chi (u i) else 1) =
      (if i<q then chi (u i) else 1)*(if i=q then 1-chi (u q) else 1) := by
    by_cases hi : i<q
    · simp [hi,ne_of_lt hi]
    · by_cases he : i=q
      · subst i; simp
      · simp [hi,he]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  have hn : (∏ i : Fin N, if i=q then 1-chi (u q) else 1)=1-chi (u q) := by simp
  rw [hn]
  have hp : (∏ i : Fin N, if i<q then chi (u i) else 1)=
      ∏ i ∈ Finset.univ.filter (fun i : Fin N => i<q), chi (u i) := by rw [Finset.prod_ite]; simp
  rw [hp,hprefix]
  unfold outerAnchor
  rw [finiteExtension_fin]
  ring

def sectorOuterRole {N : ℕ} (q i : Fin N) : Fin 3 := if i<q then 0 else if i=q then 1 else 2

theorem outerSectorScalar_product {N : ℕ} (b outer : ℝ) (ho : 0 < outer) (q : Fin N) (u : Fin N → ℝ) :
    (∏ i, outerSectorScalar b outer ho (sectorOuterRole q i) (u i))=sectorOuterAnchor b outer ho q u := by
  rw [sectorOuterAnchor,outerAnchor_coordinate_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i<q
  · simp [sectorOuterRole,outerSectorScalar,hi]
  · by_cases he : i=q <;> simp [sectorOuterRole,outerSectorScalar,hi,he]

theorem selectorSectorScalar_original_product {N : ℕ} (f : SelectorFunctions) (u : Fin N → ℝ) :
    (∏ i,selectorSectorScalar f 1 (u i))=angularSelector f u := by
  simp [selectorSectorScalar,angularSelector,selectorWeight]

theorem selectorSectorScalar_current_product {N : ℕ} (f : SelectorFunctions) (q : Fin N) (u : Fin N → ℝ) :
    (∏ i,selectorSectorScalar f (if i=q then 2 else 1) (u i))=namedSelectorDerivative f q u := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  simp only [ite_true,selectorSectorScalar,show (2:Fin 3) ≠ 0 by decide,
    show (2:Fin 3) ≠ 1 by decide,ite_false]
  unfold namedSelectorDerivative
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [Finset.ne_of_mem_erase hi]


theorem sectorScalarFamily_product {N : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (q : Fin N) (sigma role : Fin N → Fin 3) (u : Fin N → ℝ) :
    (∏ i, sectorScalarFamily f b outer inner ho hi (sectorOuterRole q i,sigma i,role i) (u i))=
      nestedSectorWeight b outer inner ho hi q sigma u * ∏ i, selectorSectorScalar f (role i) (u i) := by
  simp only [sectorScalarFamily,Finset.prod_mul_distrib,outerSectorScalar_product]
  rfl

theorem nested_sector_cutoff_jet_bounds (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ q : Fin N, ∀ sigma : Fin N → Fin 3,
      ∀ l : List (Fin N), l.length≤J → ∀ u : Fin N → ℝ,
        ‖cutoffJet l (nestedSectorWeight b outer inner ho hi q sigma) u‖ ≤ C^N ∧
        ‖cutoffJet l (fun x => angularSelector f x*nestedSectorWeight b outer inner ho hi q sigma x) u‖ ≤ C^N ∧
        ∀ qS : Fin N,
          ‖cutoffJet l (fun x => namedSelectorDerivative f qS x*nestedSectorWeight b outer inner ho hi q sigma x) u‖ ≤ C^N := by
  let g := sectorScalarFamily f b outer inner ho hi
  obtain ⟨C,hC,hbound⟩ := finite_periodic_factor_product_jets g
    (fun label => (sectorScalarFamily_regular f hf b outer inner ho hi label).1)
    (fun label => (sectorScalarFamily_regular f hf b outer inner ho hi label).2) J
  refine ⟨C,hC,?_⟩
  intro N q sigma l hl u
  have hraw : (fun x : Fin N → ℝ => ∏ i, g (sectorOuterRole q i,sigma i,(0:Fin 3)) (x i))=
      nestedSectorWeight b outer inner ho hi q sigma := by
    funext x
    rw [sectorScalarFamily_product]
    simp [selectorSectorScalar]
  have hsel : (fun x : Fin N → ℝ => ∏ i, g (sectorOuterRole q i,sigma i,(1:Fin 3)) (x i))=
      (fun x => angularSelector f x*nestedSectorWeight b outer inner ho hi q sigma x) := by
    funext x
    rw [sectorScalarFamily_product,selectorSectorScalar_original_product,mul_comm]
  have hcur (qS : Fin N) : (fun x : Fin N → ℝ =>
      ∏ i, g (sectorOuterRole q i,sigma i,if i=qS then (2:Fin 3) else 1) (x i))=
      (fun x => namedSelectorDerivative f qS x*nestedSectorWeight b outer inner ho hi q sigma x) := by
    funext x
    rw [sectorScalarFamily_product,selectorSectorScalar_current_product,mul_comm]
  constructor
  · rw [← hraw]
    exact hbound N (fun i => (sectorOuterRole q i,sigma i,(0:Fin 3))) l hl u
  constructor
  · rw [← hsel]
    exact hbound N (fun i => (sectorOuterRole q i,sigma i,(1:Fin 3))) l hl u
  · intro qS
    rw [← hcur qS]
    exact hbound N (fun i => (sectorOuterRole q i,sigma i,if i=qS then (2:Fin 3) else 1)) l hl u


theorem scalar_product_coordinate_periodic {I : Type*} (g : I → ℝ → ℝ)
    (hp : ∀ a, Function.Periodic (g a) (2*Real.pi)) {N : ℕ} (labels : Fin N → I)
    (theta : Fin N → ℝ) (q : Fin N) :
    (∏ i, g (labels i) (Function.update theta q (theta q+2*Real.pi) i)) = ∏ i, g (labels i) (theta i) := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=q
  · subst i
    rw [Function.update_self]
    exact hp (labels q) (theta q)
  · rw [Function.update_of_ne hi]

theorem nested_sector_weights_periodic (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) {N : ℕ}
    (q : Fin N) (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) (i : Fin N) :
    let theta' := Function.update theta i (theta i+2*Real.pi)
    nestedSectorWeight b outer inner ho hi q sigma theta'=nestedSectorWeight b outer inner ho hi q sigma theta ∧
    angularSelector f theta'*nestedSectorWeight b outer inner ho hi q sigma theta'=
      angularSelector f theta*nestedSectorWeight b outer inner ho hi q sigma theta ∧
    ∀ qS : Fin N, namedSelectorDerivative f qS theta'*nestedSectorWeight b outer inner ho hi q sigma theta'=
      namedSelectorDerivative f qS theta*nestedSectorWeight b outer inner ho hi q sigma theta := by
  have hp := fun label => (sectorScalarFamily_regular f hf b outer inner ho hi label).2
  have hraw := scalar_product_coordinate_periodic _ hp (fun k => (sectorOuterRole q k,sigma k,(0:Fin 3))) theta i
  have hsel := scalar_product_coordinate_periodic _ hp (fun k => (sectorOuterRole q k,sigma k,(1:Fin 3))) theta i
  have hcur (qS : Fin N) := scalar_product_coordinate_periodic _ hp
    (fun k => (sectorOuterRole q k,sigma k,if k=qS then (2:Fin 3) else 1)) theta i
  simp_rw [sectorScalarFamily_product] at hraw hsel hcur
  constructor
  · simpa only [selectorSectorScalar,ite_true,Finset.prod_const_one,mul_one] using hraw
  constructor
  · simpa only [selectorSectorScalar_original_product,mul_comm] using hsel
  · intro qS
    simpa only [selectorSectorScalar_current_product,mul_comm] using hcur qS

end
end IsingBulk.Tail
