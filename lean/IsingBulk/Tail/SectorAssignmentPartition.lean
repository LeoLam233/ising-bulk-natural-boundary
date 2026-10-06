import IsingBulk.Tail.SectorPartitionSupport

/-! Exact finite product partition with source-fixed real angular weights.
All labels survive every finite cutoff jet; no analytic assignment domains
are introduced or differentiated. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Function
open scoped BigOperators ContDiff Topology

def sectorLabel (b delta : ℝ) (hd : 0 < delta) (c : Fin 3) (theta : ℝ) : ℝ :=
  if c=0 then sectorLeft b delta hd theta else if c=1 then sectorRight b delta hd theta
  else sectorBranch b delta hd theta

def sectorAssignmentWeight {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) : ℝ :=
  ∏ i, sectorLabel b delta hd (sigma i) (theta i)

theorem sectorLabel_sum (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) :
    (∑ c : Fin 3, sectorLabel b delta hd c theta)=1 := by
  simpa [sectorLabel,Fin.sum_univ_succ,add_assoc] using sector_partition b delta hd theta

theorem sector_assignment_partition (N : ℕ) (b delta : ℝ) (hd : 0 < delta)
    (theta : Fin N → ℝ) :
    (∑ sigma : Fin N → Fin 3, sectorAssignmentWeight b delta hd sigma theta)=1 := by
  simp only [sectorAssignmentWeight]
  rw [← Fintype.prod_sum (fun i : Fin N => fun c : Fin 3 => sectorLabel b delta hd c (theta i))]
  simp only [sectorLabel_sum,Finset.prod_const_one]

theorem sector_assignment_nonnegative {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) :
    0 ≤ sectorAssignmentWeight b delta hd sigma theta := by
  apply Finset.prod_nonneg
  intro i hi
  obtain ⟨hL,hR,hB⟩ := sector_labels_nonnegative b delta hd (theta i)
  unfold sectorLabel
  split_ifs <;> assumption

theorem sector_assignment_smooth {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (sigma : Fin N → Fin 3) : ContDiff ℝ ∞ (sectorAssignmentWeight b delta hd sigma) := by
  apply contDiff_prod
  intro i hi
  obtain ⟨hL,hR,hB⟩ := sector_labels_smooth b delta hd
  unfold sectorLabel
  split_ifs
  · exact hL.comp (contDiff_apply ℝ ℝ i)
  · exact hR.comp (contDiff_apply ℝ ℝ i)
  · exact hB.comp (contDiff_apply ℝ ℝ i)

theorem sector_assignment_tsupport {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (sigma : Fin N → Fin 3) :
    tsupport (sectorAssignmentWeight b delta hd sigma) ⊆
      {theta | ∀ i, theta i ∈ tsupport (sectorLabel b delta hd (sigma i))} := by
  apply closure_minimal
  · intro theta htheta i
    exact subset_closure (Finset.prod_ne_zero_iff.mp htheta i (Finset.mem_univ i))
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))

theorem sector_assignment_cutoff_jets_support {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (sigma : Fin N → Fin 3) (l : List (Fin N)) :
    tsupport (cutoffJet l (sectorAssignmentWeight b delta hd sigma)) ⊆
      {theta | ∀ i, theta i ∈ tsupport (sectorLabel b delta hd (sigma i))} :=
  (cutoffJet_tsupport_subset l _).trans (sector_assignment_tsupport b delta hd sigma)

theorem sector_all_branch_micro_plateau {N : ℕ} (b delta : ℝ) (hd : 0 < delta)
    (u : Fin N → ℝ) (hu : ∀ i, |u i| ≤ delta/2) :
    sectorAssignmentWeight b delta hd (fun _ : Fin N => (2:Fin 3)) (fun i => -b+u i)=1 := by
  apply Finset.prod_eq_one
  intro i hi
  simpa only [sectorLabel,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide,
    ite_false] using sectorBranch_lower_plateau b delta hd (hu i)

end
end IsingBulk.Tail
