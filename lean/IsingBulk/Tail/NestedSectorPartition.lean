import IsingBulk.Tail.SectorAssignmentPartition
import Mathlib.Algebra.BigOperators.Fin

/-! Nested outer-anchor/inner-sector partition. The outer anchor is fixed
before differentiation; an inner true-branch label is separated from it.
Quantitative dispersion-slope domination is attached downstream. -/
namespace IsingBulk.Tail
noncomputable section
open Set Function IsingBulk.Jets
open scoped BigOperators ContDiff Topology

def finiteExtension {N : ℕ} (f : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then f ⟨i,h⟩ else 0

theorem finiteExtension_fin {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : finiteExtension f i=f i := by
  simp [finiteExtension,i.isLt]

def sectorOuterAnchor {N : ℕ} (b delta : ℝ) (hd : 0 < delta) (q : Fin N)
    (theta : Fin N → ℝ) : ℝ :=
  outerAnchor (finiteExtension (fun i => sectorBranch b delta hd (theta i))) q

theorem sector_outer_telescope {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (theta : Fin N → ℝ) :
    (∏ i, sectorBranch b delta hd (theta i)) + (∑ q : Fin N, sectorOuterAnchor b delta hd q theta)=1 := by
  have hh := outerAnchor_telescope (finiteExtension (fun i => sectorBranch b delta hd (theta i))) N
  rw [← Fin.prod_univ_eq_prod_range,← Fin.sum_univ_eq_sum_range] at hh
  simpa only [finiteExtension_fin,sectorOuterAnchor] using hh

theorem sectorOuterAnchor_smooth {N : ℕ} (b delta : ℝ) (hd : 0 < delta) (q : Fin N) :
    ContDiff ℝ ∞ (sectorOuterAnchor b delta hd q) := by
  have hc (i : ℕ) : ContDiff ℝ ∞ (fun theta : Fin N → ℝ =>
      finiteExtension (fun j => sectorBranch b delta hd (theta j)) i) := by
    by_cases hi : i < N
    · simp only [finiteExtension,dite_eq_left hi]
      exact (sector_labels_smooth b delta hd).2.2.comp (contDiff_apply ℝ ℝ (⟨i,hi⟩ : Fin N))
    · simp only [finiteExtension,dite_eq_right hi]
      exact contDiff_const
  exact (contDiff_const.sub (hc q)).mul (contDiff_prod (fun i _ => hc i))

theorem sectorOuterAnchor_tsupport {N : ℕ} (b delta : ℝ) (hd : 0 < delta) (q : Fin N) :
    tsupport (sectorOuterAnchor b delta hd q) ⊆
      {theta | delta/2 ≤ |sectorDisplacement b (theta q)|} := by
  apply closure_minimal
  · intro theta htheta
    have hnon := outerAnchor_ne_zero
      (finiteExtension (fun i => sectorBranch b delta hd (theta i))) q htheta
    rw [finiteExtension_fin] at hnon
    by_contra hn
    have ht : |sectorDisplacement b (theta q)| ≤ delta/2 := (lt_of_not_ge hn).le
    exact hnon (fixedBranchBump_one delta hd ht)
  · exact isClosed_le continuous_const (by unfold sectorDisplacement; fun_prop)

theorem sectorOuterAnchor_jet_tsupport {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (q : Fin N) (l : List (Fin N)) :
    tsupport (cutoffJet l (sectorOuterAnchor b delta hd q)) ⊆
      {theta | delta/2 ≤ |sectorDisplacement b (theta q)|} :=
  (cutoffJet_tsupport_subset l _).trans (sectorOuterAnchor_tsupport b delta hd q)

def nestedSectorWeight {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (q : Fin N) (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) : ℝ :=
  sectorOuterAnchor b outer ho q theta*sectorAssignmentWeight b inner hi sigma theta

theorem nested_sector_partition {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (theta : Fin N → ℝ) :
    (∏ i, sectorBranch b outer ho (theta i)) +
      (∑ q : Fin N, ∑ sigma : Fin N → Fin 3, nestedSectorWeight b outer inner ho hi q sigma theta)=1 := by
  simp only [nestedSectorWeight,← Finset.mul_sum,sector_assignment_partition,mul_one]
  exact sector_outer_telescope b outer ho theta

theorem nested_anchor_not_inner_branch {N : ℕ} (b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (hio : inner ≤ outer/4)
    (q : Fin N) (theta : Fin N → ℝ)
    (hanchor : theta ∈ tsupport (sectorOuterAnchor b outer ho q)) :
    theta q ∉ tsupport (sectorBranch b inner hi) := by
  intro hbranch
  have ha := sectorOuterAnchor_tsupport b outer ho q hanchor
  have hb := (sector_labels_tsupport b inner hi).2.2 hbranch
  change outer/2 ≤ |sectorDisplacement b (theta q)| at ha
  change |sectorDisplacement b (theta q)| ≤ inner at hb
  linarith


theorem nested_sector_label_count (N : ℕ) :
    Fintype.card (Option (Fin N × (Fin N → Fin 3))) ≤ 12^N := by
  simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  cases N with
  | zero => norm_num
  | succ n =>
    have hN : n+1 ≤ 2^(n+1) := (Nat.lt_two_pow_self : n+1 < 2^(n+1)).le
    have htwo : 2 ≤ 2^(n+1) := by
      rw [pow_succ]
      have hh : (1:ℕ) ≤ (2:ℕ)^n := Nat.one_le_pow n 2 (by decide)
      omega
    have hp : (1:ℕ) ≤ (6:ℕ)^(n+1) := Nat.one_le_pow (n+1) 6 (by decide)
    calc
      _ ≤ 2^(n+1)*3^(n+1)+1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hN) 1
      _ = 6^(n+1)+1 := by rw [← mul_pow]; norm_num
      _ ≤ 2*6^(n+1) := by omega
      _ ≤ 2^(n+1)*6^(n+1) := Nat.mul_le_mul_right _ htwo
      _ = _ := by rw [← mul_pow]; norm_num


theorem nested_sector_jet_support {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (q : Fin N) (sigma : Fin N → Fin 3) (l : List (Fin N)) :
    tsupport (cutoffJet l (nestedSectorWeight b outer inner ho hi q sigma)) ⊆
      tsupport (sectorOuterAnchor b outer ho q) ∩ tsupport (sectorAssignmentWeight b inner hi sigma) := by
  intro theta htheta
  have hh := cutoffJet_tsupport_subset l (nestedSectorWeight b outer inner ho hi q sigma) htheta
  exact ⟨tsupport_mul_subset_left hh,tsupport_mul_subset_right hh⟩

theorem nested_sector_named_nonbranch {N : ℕ} (b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (hio : inner ≤ outer/4)
    (q : Fin N) (sigma : Fin N → Fin 3) (l : List (Fin N)) (theta : Fin N → ℝ)
    (htheta : theta ∈ tsupport (cutoffJet l (nestedSectorWeight b outer inner ho hi q sigma))) :
    sigma q ≠ 2 := by
  obtain ⟨ha,hs⟩ := nested_sector_jet_support b outer inner ho hi q sigma l htheta
  intro heq
  have hB := sector_assignment_tsupport b inner hi sigma hs q
  simp only [heq] at hB
  exact nested_anchor_not_inner_branch b outer inner ho hi hio q theta ha hB

theorem nested_sector_three_types {N : ℕ} (b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (hio : inner ≤ outer/4)
    (q : Fin N) (sigma : Fin N → Fin 3) (l : List (Fin N)) (theta : Fin N → ℝ)
    (htheta : theta ∈ tsupport (cutoffJet l (nestedSectorWeight b outer inner ho hi q sigma))) :
    (∃ i, sigma i=0) ∨ (sigma q=1 ∧ ∃ j, j ≠ q ∧ sigma j=2) ∨ (∀ i, sigma i=1) := by
  classical
  have hq := nested_sector_named_nonbranch b outer inner ho hi hio q sigma l theta htheta
  by_cases hleft : ∃ i, sigma i=0
  · exact Or.inl hleft
  have hnotleft (i : Fin N) : sigma i ≠ 0 := fun hi => hleft ⟨i,hi⟩
  have hqright : sigma q=1 := by
    have hn := hnotleft q
    generalize hc : sigma q=c at *
    fin_cases c <;> simp_all
  by_cases hbranch : ∃ j, sigma j=2
  · obtain ⟨j,hj⟩ := hbranch
    exact Or.inr (Or.inl ⟨hqright,j,by intro he; subst j; exact hq hj,hj⟩)
  · refine Or.inr (Or.inr ?_)
    intro i
    have hn := hnotleft i
    have hb : sigma i ≠ 2 := fun hi => hbranch ⟨i,hi⟩
    generalize hc : sigma i=c at *
    fin_cases c <;> simp_all

end
end IsingBulk.Tail
