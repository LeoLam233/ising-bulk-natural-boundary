import IsingBulk.Tail.AllBranchExteriorCutoffs
import IsingBulk.Tail.AllBranchExteriorShape
import IsingBulk.Tail.CompactSupportLie

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Function
open scoped ContDiff Topology

def allBranchSelectedGuard {N : ℕ} (h : ℝ) (p q : Fin N) (u : Fin N → ℝ) : ℝ :=
  1-microCutoffBase ((u p-u q)/h)

theorem allBranchSelectedGuard_smooth {N : ℕ} (h : ℝ) (p q : Fin N) :
    ContDiff ℝ ∞ (allBranchSelectedGuard h p q) := by
  exact contDiff_const.sub ((fixedBranchBump 1 (by norm_num)).contDiff.comp
    (((contDiff_apply ℝ ℝ p).sub (contDiff_apply ℝ ℝ q)).div_const h))

theorem allBranchSelectedGuard_tsupport {N : ℕ} {h : ℝ} (hh : 0 < h) (p q : Fin N) :
    tsupport (allBranchSelectedGuard h p q) ⊆ {u | h/2 ≤ |u p-u q|} := by
  apply closure_minimal
  · intro u hu
    by_contra hn
    change ¬ h/2 ≤ |u p-u q| at hn
    have hsmall : |(u p-u q)/h| ≤ 1/2 := by
      rw [abs_div,abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr (by linarith [lt_of_not_ge hn])
    have he := fixedBranchBump_one 1 (by norm_num) hsmall
    exact hu (by simp [allBranchSelectedGuard,microCutoffBase,he])
  · exact isClosed_le continuous_const (((continuous_apply p).sub (continuous_apply q)).abs)

def allBranchTruncationGate {N : ℕ} (h : ℝ) (p q : Fin N) (w : (Fin N → ℝ) → ℝ)
    (u : Fin N → ℝ) : ℝ := (w u*allBranchSelectedGuard h p q u)*branchFarCutoff h u

def allBranchTruncatedWeight {N : ℕ} (M : ℕ) (h : ℝ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) : ℝ :=
  allBranchTruncationGate h p q w u*allBranchExteriorPairWeight M p q u

theorem allBranchTruncationGate_smooth {N : ℕ} (h : ℝ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (allBranchTruncationGate h p q w) :=
  (hw.mul (allBranchSelectedGuard_smooth h p q)).mul (branch_shape_cutoffs_smooth h).1

theorem allBranchTruncationGate_support {N : ℕ} {h : ℝ} (hh : 0 < h) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) {u : Fin N → ℝ} (hu : u ∈ tsupport (allBranchTruncationGate h p q w)) :
    u ∈ tsupport w ∧ h/2 ≤ |u p-u q| ∧ h ≤ branchShapeRadius u := by
  have hleft : u ∈ tsupport (fun x => w x*allBranchSelectedGuard h p q x) := tsupport_mul_subset_left hu
  have hright : u ∈ tsupport (branchFarCutoff h) := tsupport_mul_subset_right hu
  exact ⟨tsupport_mul_subset_left hleft,
    allBranchSelectedGuard_tsupport hh p q (tsupport_mul_subset_right hleft),
    branch_far_jet_support hh [] hright⟩

theorem allBranchTruncatedWeight_smooth {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h)
    (p q : Fin N) (w : (Fin N → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (allBranchTruncatedWeight M h p q w) := by
  have hN : 0 < N := Nat.zero_lt_of_lt p.isLt
  have hg := allBranchTruncationGate_smooth h p q w hw
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport (allBranchTruncationGate h p q w)
  · have hd := (allBranchExterior_far_diameter_pos hN u h hh
      (allBranchTruncationGate_support hh p q w hu).2.2).2
    exact hg.contDiffAt.mul (allBranchExterior_pairWeight_contDiffAt M p q u hd)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hu
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with x hx
    change allBranchTruncationGate h p q w x*allBranchExteriorPairWeight M p q x=0
    simp only [hx,Pi.zero_apply,zero_mul]

theorem allBranchTruncatedWeight_support {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h)
    (p q : Fin N) (w : (Fin N → ℝ) → ℝ) {u : Fin N → ℝ}
    (hu : u ∈ tsupport (allBranchTruncatedWeight M h p q w)) :
    u ∈ tsupport w ∧ h/2 ≤ |u p-u q| ∧ h ≤ branchShapeRadius u :=
  allBranchTruncationGate_support hh p q w (tsupport_mul_subset_left hu)

end
end IsingBulk.Tail
