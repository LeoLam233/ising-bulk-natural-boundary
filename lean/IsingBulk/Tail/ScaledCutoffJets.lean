import IsingBulk.Tail.NestedCutoffs
import IsingBulk.Analysis.JetsTermPullback
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-! The fixed source cutoff is scaled explicitly before taking real jets.
Bounds are uniform in dimension and scale; no variable bump family is
silently identified with a dilation of a fixed function. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Function
open scoped BigOperators ContDiff Topology

abbrev microCutoffBase : ℝ → ℝ := fixedBranchBump 1 (by norm_num)

theorem microCutoffBase_iterated_support (k : ℕ) :
    tsupport (iteratedDeriv k microCutoffBase) ⊆ Icc (-1:ℝ) 1 := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero]
    apply closure_minimal _ isClosed_Icc
    intro u hu
    have ht := fixedBranchBump_support 1 (by norm_num) hu
    exact ⟨(abs_lt.mp ht).1.le,(abs_lt.mp ht).2.le⟩
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem microCutoffBase_derivatives_bounded (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, k ≤ j → ∀ u : ℝ,
      ‖iteratedDeriv k microCutoffBase u‖ ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, ∀ u : ℝ, ‖iteratedDeriv k microCutoffBase u‖ ≤ C := by
    have hc : Continuous (iteratedDeriv k microCutoffBase) :=
      (show ContDiff ℝ ∞ microCutoffBase from (fixedBranchBump 1 (by norm_num)).contDiff).continuous_iteratedDeriv k (by simp)
    have hs : HasCompactSupport (iteratedDeriv k microCutoffBase) :=
      isCompact_Icc.of_isClosed_subset isClosed_closure (microCutoffBase_iterated_support k)
    exact hc.bounded_above_of_compact_support hs
  induction j with
  | zero =>
    obtain ⟨C,hC⟩ := hb 0
    exact ⟨max 1 C,le_max_left _ _,fun k hk u => by
      have he : k=0 := by omega
      simpa only [he] using (hC u).trans (le_max_right 1 C)⟩
  | succ j ih =>
    obtain ⟨C,hC,hj⟩ := ih
    obtain ⟨D,hD⟩ := hb (j+1)
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro k hk u
    by_cases hkj : k ≤ j
    · exact (hj k hkj u).trans (le_max_left _ _)
    · have he : k=j+1 := by omega
      exact he ▸ (hD u).trans (le_max_right _ _)

def scaledCutoffFactor (b : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (b⁻¹)^k*iteratedDeriv k microCutoffBase (u/b)

theorem scaledCutoffFactor_hasDerivAt (b : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (scaledCutoffFactor b k) (scaledCutoffFactor b (k+1) u) u := by
  have hd := ((show ContDiff ℝ ∞ microCutoffBase from (fixedBranchBump 1 (by norm_num)).contDiff).differentiable_iteratedDeriv k
    (by exact_mod_cast (ENat.natCast_lt_top k)) (u/b)).hasDerivAt
  have hh := (hd.comp u ((hasDerivAt_id u).div_const b)).const_mul ((b⁻¹)^k)
  convert hh using 1
  · rfl
  · simp only [scaledCutoffFactor,iteratedDeriv_succ,pow_succ,div_eq_mul_inv]
    ring

theorem coordinate_product_fderiv {N : ℕ} (g : Fin N → ℝ → ℝ)
    (hg : ∀ i, Differentiable ℝ (g i)) (q : Fin N) (u : Fin N → ℝ) :
    fderiv ℝ (fun x : Fin N → ℝ => ∏ i, g i (x i)) u (Pi.single q 1) =
      deriv (g q) (u q) * ∏ i ∈ Finset.univ.erase q, g i (u i) := by
  classical
  have hprod : DifferentiableAt ℝ (fun x : Fin N → ℝ => ∏ i, g i (x i)) u := by
    exact (HasFDerivAt.finsetProd (fun i (_ : i ∈ Finset.univ) =>
      ((hg i (u i)).comp u (differentiableAt_apply i u)).hasFDerivAt)).differentiableAt
  have hat : HasFDerivAt (fun x : Fin N → ℝ => ∏ i, g i (x i))
      (fderiv ℝ (fun x : Fin N → ℝ => ∏ i, g i (x i)) u) (Function.update u q (u q)) := by
    simpa only [Function.update_eq_self] using hprod.hasFDerivAt
  have hc := hat.comp_hasDerivAt (u q) (hasDerivAt_update u q (u q))
  have he : (fun t : ℝ => ∏ i : Fin N, g i (Function.update u q t i)) =
      (fun t => g q t * ∏ i ∈ Finset.univ.erase q, g i (u i)) := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.comp_def] at hc
  rw [he] at hc
  exact hc.deriv.symm.trans (((hg q (u q)).hasDerivAt.mul_const _).deriv)


def scaledMicroCutoff (N : ℕ) (b : ℝ) (u : Fin N → ℝ) : ℝ :=
  ∏ i, microCutoffBase (u i/b)

theorem cutoffJet_scaledMicroCutoff {N : ℕ} (b : ℝ) (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (scaledMicroCutoff N b) u =
      ∏ i, scaledCutoffFactor b (l.count i) (u i) := by
  induction l generalizing u with
  | nil => simp [cutoffJet,scaledMicroCutoff,scaledCutoffFactor]
  | cons q l ih =>
    have he : cutoffJet l (scaledMicroCutoff N b) =
        (fun u => ∏ i, scaledCutoffFactor b (l.count i) (u i)) := funext ih
    rw [cutoffJet,he]
    dsimp only
    rw [coordinate_product_fderiv _
      (fun i x => (scaledCutoffFactor_hasDerivAt b (l.count i) x).differentiableAt)]
    rw [(scaledCutoffFactor_hasDerivAt b (l.count q) (u q)).deriv]
    symm
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    congr 1
    · simp only [List.count_cons_self]
    · apply Finset.prod_congr rfl
      intro i hi
      have hne : q ≠ i := (Finset.ne_of_mem_erase hi).symm
      simp only [List.count_cons_of_ne hne]

theorem list_sum_coordinate_counts {N : ℕ} (l : List (Fin N)) :
    (∑ i : Fin N, l.count i)=l.length := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.count_cons,List.length_cons]
    rw [Finset.sum_add_distrib,ih]
    simp

theorem scaledMicroCutoff_smooth (N : ℕ) (b : ℝ) : ContDiff ℝ ∞ (scaledMicroCutoff N b) := by
  apply contDiff_prod
  intro i hi
  exact (fixedBranchBump 1 (by norm_num)).contDiff.comp ((contDiff_apply ℝ ℝ i).div_const b)



theorem scaledMicroCutoff_jet_bound (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∀ l : List (Fin N), l.length ≤ j → ∀ u : Fin N → ℝ,
        ‖cutoffJet l (scaledMicroCutoff N b) u‖ ≤ C^N*(b⁻¹)^j := by
  obtain ⟨C,hC,hder⟩ := microCutoffBase_derivatives_bounded j
  refine ⟨C,hC,?_⟩
  intro N b hb hb1 l hl u
  rw [cutoffJet_scaledMicroCutoff,norm_prod]
  have hf (i : Fin N) : ‖scaledCutoffFactor b (l.count i) (u i)‖ ≤
      (b⁻¹)^(l.count i)*C := by
    rw [scaledCutoffFactor,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)]
    exact mul_le_mul_of_nonneg_left (hder _ ((List.count_le_length).trans hl) _) (by positivity)
  calc
    _ ≤ ∏ i : Fin N, (b⁻¹)^(l.count i)*C :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i)
    _ = C^N*(b⁻¹)^l.length := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,list_sum_coordinate_counts]
      simp [mul_comm]
    _ ≤ C^N*(b⁻¹)^j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ ((one_le_inv₀ hb).mpr hb1) hl

theorem scaledMicroCutoff_jet_tsupport {N : ℕ} {b : ℝ} (hb : 0 < b)
    (l : List (Fin N)) :
    tsupport (cutoffJet l (scaledMicroCutoff N b)) ⊆ {u | ∀ i, |u i| ≤ b} := by
  classical
  apply closure_minimal
  · intro u hu i
    change cutoffJet l (scaledMicroCutoff N b) u ≠ 0 at hu
    rw [cutoffJet_scaledMicroCutoff] at hu
    have hi := Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
    have hder : iteratedDeriv (l.count i) microCutoffBase (u i/b) ≠ 0 :=
      (mul_ne_zero_iff.mp hi).2
    have hm := microCutoffBase_iterated_support (l.count i) (subset_closure hder)
    have habs : |u i/b| ≤ 1 := abs_le.mpr hm
    rw [abs_div,abs_of_pos hb] at habs
    exact (div_le_one hb).mp habs
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (continuous_apply i).abs continuous_const)


end
end IsingBulk.Tail
