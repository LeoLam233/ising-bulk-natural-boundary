import IsingBulk.Tail.IndexedPairCounting
import IsingBulk.Tail.AllBranchExteriorJets
import Mathlib.Data.Finset.Lattice.Fold

/-! Literal rational selected-pair weights. Their smoothness is asserted
only off full equality; no globally smooth rational cutoff is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open Set IsingBulk.Jets
open scoped BigOperators ContDiff

def allBranchExteriorDiameterNN {N : ℕ} (u : Fin N → ℝ) : NNReal :=
  Finset.univ.sup (fun p : Fin N × Fin N => ‖u p.1-u p.2‖₊)

def allBranchExteriorDiameter {N : ℕ} (u : Fin N → ℝ) : ℝ := allBranchExteriorDiameterNN u

def allBranchExteriorWeightDenom {N : ℕ} (M : ℕ) (u : Fin N → ℝ) : ℝ :=
  ∑ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), (u p.1-u p.2)^(2*M)

def allBranchExteriorPairWeight {N : ℕ} (M : ℕ) (p q : Fin N) (u : Fin N → ℝ) : ℝ :=
  (u p-u q)^(2*M)/allBranchExteriorWeightDenom M u

theorem allBranchExterior_pair_le_diameter {N : ℕ} (u : Fin N → ℝ) (p q : Fin N) :
    |u p-u q| ≤ allBranchExteriorDiameter u := by
  have hh := Finset.le_sup (s := (Finset.univ : Finset (Fin N × Fin N)))
    (f := fun r : Fin N × Fin N => ‖u r.1-u r.2‖₊) (Finset.mem_univ (p,q))
  have hc := NNReal.coe_le_coe.mpr hh
  simpa [allBranchExteriorDiameter,allBranchExteriorDiameterNN,Real.norm_eq_abs] using hc

theorem allBranchExterior_diameter_attained {N : ℕ} (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) :
    ∃ p q : Fin N, p < q ∧ |u p-u q|=allBranchExteriorDiameter u := by
  have hpos : (0:NNReal) < allBranchExteriorDiameterNN u := hu
  obtain ⟨⟨p,q⟩,_,hh⟩ := (Finset.le_sup_iff hpos).mp (le_refl (allBranchExteriorDiameterNN u))
  have hle : allBranchExteriorDiameter u ≤ |u p-u q| := by exact_mod_cast hh
  have he := le_antisymm (allBranchExterior_pair_le_diameter u p q) hle
  have hpq : p ≠ q := by intro heq; subst q; simp at he; linarith
  rcases lt_or_gt_of_ne hpq with hpq|hqp
  · exact ⟨p,q,hpq,he⟩
  · exact ⟨q,p,hqp,by simpa only [abs_sub_comm] using he⟩

theorem allBranchExterior_weightDenom_nonneg {N : ℕ} (M : ℕ) (u : Fin N → ℝ) :
    0 ≤ allBranchExteriorWeightDenom M u := by
  apply Finset.sum_nonneg
  intro p _
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg (u p.1-u p.2)) M

theorem allBranchExterior_weightDenom_diameter_lower {N : ℕ} (M : ℕ) (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) :
    allBranchExteriorDiameter u^(2*M) ≤ allBranchExteriorWeightDenom M u := by
  obtain ⟨p,q,hpq,he⟩ := allBranchExterior_diameter_attained u hu
  have hmem : (p,q) ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) := by simp [orderedIndexPairs,hpq]
  have hh := Finset.single_le_sum (s := orderedIndexPairs (Finset.univ : Finset (Fin N)))
    (f := fun r : Fin N × Fin N => (u r.1-u r.2)^(2*M))
    (fun r _ => (show 0 ≤ (u r.1-u r.2)^(2*M) by rw [pow_mul]; positivity)) hmem
  have hp : (u p-u q)^(2*M)=allBranchExteriorDiameter u^(2*M) := by
    rw [← he,pow_mul,pow_mul,sq_abs]
  rw [hp] at hh
  exact hh

theorem allBranchExterior_weightDenom_pos {N : ℕ} (M : ℕ) (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) : 0 < allBranchExteriorWeightDenom M u :=
  (pow_pos hu _).trans_le (allBranchExterior_weightDenom_diameter_lower M u hu)

theorem allBranchExterior_pairWeight_nonneg {N : ℕ} (M : ℕ) (p q : Fin N) (u : Fin N → ℝ) :
    0 ≤ allBranchExteriorPairWeight M p q u := by
  apply div_nonneg _ (allBranchExterior_weightDenom_nonneg M u)
  rw [pow_mul]
  positivity

theorem allBranchExterior_pairWeight_sum {N : ℕ} (M : ℕ) (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) :
    (∑ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), allBranchExteriorPairWeight M p.1 p.2 u)=1 := by
  unfold allBranchExteriorPairWeight
  rw [← Finset.sum_div]
  exact div_self (allBranchExterior_weightDenom_pos M u hu).ne'

theorem allBranchExterior_pairWeight_contDiffAt {N : ℕ} (M : ℕ) (p q : Fin N) (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) : ContDiffAt ℝ ∞ (allBranchExteriorPairWeight M p q) u := by
  have hn : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (x p-x q)^(2*M)) := by fun_prop
  have hd : ContDiff ℝ ∞ (allBranchExteriorWeightDenom (N := N) M) := by unfold allBranchExteriorWeightDenom; fun_prop
  exact hn.contDiffAt.div hd.contDiffAt (allBranchExterior_weightDenom_pos M u hu).ne'

theorem allBranchExterior_pairWeight_zero {N : ℕ} (M : ℕ) (hM : 0 < M) (p q : Fin N)
    (u : Fin N → ℝ) (hpq : u p=u q) : allBranchExteriorPairWeight M p q u=0 := by
  simp [allBranchExteriorPairWeight,hpq,show 2*M≠0 by omega]

end
end IsingBulk.Tail
