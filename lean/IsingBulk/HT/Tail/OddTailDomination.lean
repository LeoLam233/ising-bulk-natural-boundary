import IsingBulk.HT.Tail.OddIndexing

/-!
# Exact odd infinite-tail source comparison

This is the all-order F+K+S comparison for the actual positive-kernel
source, with the HT first order `p` rather than LT's `2*p`.  The only
series hypotheses are exposed summability requirements for its source
pieces; no asymptotic tail bound or noncancellation is assumed or proved
by this algebraic comparison alone.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail MeasureTheory Set
open scoped Topology

def intermediateOddKSNormWindow (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) : ℝ :=
  ∑' N : ℕ, if p + 2 ≤ N ∧ (N : ℝ) < D * Real.sqrt (-Real.log eps) then
    originalKSNorm N (constructedSelector d.thetaB eta alpha)
      (Real.exp (-d.c₀ * eps)) tau j (radialParameter d.theta eps) cut else 0

set_option maxHeartbeats 1800000 in
theorem actual_higher_odd_tail_domination {p : ℕ} (hp : Odd p)
    (d : LocalBranchData) (eta alpha tau D eps cut : ℝ)
    (hf : RegularSelector (constructedSelector d.thetaB eta alpha)) (htau : 0 ≤ tau)
    (heps : 0 < eps) (hcut : cut ∈ Icc (0 : ℝ) 1)
    (hs : radialParameter d.theta eps ∈ dampingDomain (Real.exp (-d.c₀ * eps)))
    (j : ℕ)
    (hF : Summable (fun n : ℕ => ‖iteratedDeriv j
      (selectedIntegral (2 * n + 1) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀ * eps)) tau) (radialParameter d.theta eps)‖))
    (hL : Summable (fun n : ℕ => ‖∫ lam in cut..1,
      differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖))
    (hK : Summable (fun N : ℕ => if 2 ≤ N then
      originalKSNorm N (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀ * eps)) tau j (radialParameter d.theta eps) cut else 0)) :
    (∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter d.theta eps)‖) ≤
      (∑' n : ℕ, ‖iteratedDeriv j
        (selectedIntegral (2 * n + 1) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀ * eps)) tau) (radialParameter d.theta eps)‖) +
      (∑' n : ℕ, ‖∫ lam in cut..1,
        differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖) +
      intermediateOddKSNormWindow p d eta alpha tau j D eps cut +
      highKSNormTail d eta alpha tau j D eps cut := by
  let f := constructedSelector d.thetaB eta alpha
  let r := Real.exp (-d.c₀ * eps)
  let s := radialParameter d.theta eps
  let q := (p + 1) / 2
  let F := fun n : ℕ => ‖iteratedDeriv j (selectedIntegral (2 * n + 1) f r tau) s‖
  let L := fun n : ℕ => ‖∫ lam in cut..1,
    differentiatedCurrentSlice (2 * n + 1) f r tau lam j s‖
  let K := fun N : ℕ => if 2 ≤ N then originalKSNorm N f r tau j s cut else 0
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have htrace : 0 < (sourceS (radialParameter d.theta eps)).im := by
    have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
    have hm := hs.2
    change r⁻¹ - r < _ at hm
    linarith
  have hshift : Function.Injective (fun n : ℕ => n + q) :=
    fun _ _ h => Nat.add_right_cancel h
  have hu : Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s‖) := by
    simpa only [Function.comp_def, oddTailParticle_eq_index hp, q, s] using
      (upperOdd_derivative_summable j htrace).comp_injective hshift
  have hFs : Summable (fun n : ℕ => F (n + q)) := hF.comp_injective hshift
  have hLs : Summable (fun n : ℕ => L (n + q)) := hL.comp_injective hshift
  have hKs : Summable (fun n : ℕ => K (oddTailParticle p n)) :=
    hK.comp_injective (oddTailParticle_injective p)
  have hpoint (n : ℕ) : ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s‖ ≤
      F (n + q) + K (oddTailParticle p n) + L (n + q) := by
    have hN : 2 ≤ oddTailParticle p n := by dsimp [oddTailParticle]; omega
    dsimp [F, K, L]
    rw [ite_eq_left hN]
    simpa only [oddTailParticle_eq_index hp, q] using
      selector_derivative_norm_split (oddTailParticle p n) (by omega)
        f hf hr hr1 htau hcut hs j
  have hsum := Summable.tsum_le_tsum hpoint hu ((hFs.add hKs).add hLs)
  rw [(hFs.add hKs).tsum_add hLs, hFs.tsum_add hKs] at hsum
  have hFle : (∑' n : ℕ, F (n + q)) ≤ ∑' n : ℕ, F n :=
    hFs.tsum_le_tsum_of_inj (fun n => n + q) hshift
      (fun n _ => norm_nonneg _) (fun _ => le_rfl) hF
  have hLle : (∑' n : ℕ, L (n + q)) ≤ ∑' n : ℕ, L n :=
    hLs.tsum_le_tsum_of_inj (fun n => n + q) hshift
      (fun n _ => norm_nonneg _) (fun _ => le_rfl) hL
  have hK0 (N : ℕ) : 0 ≤ K N := by
    dsimp [K]
    split_ifs
    · exact originalKSNorm_nonneg _ _ _ _ _ _ _
    · exact le_rfl
  have hKle := nonnegative_odd_tail_window_split K hK0 hK p
    (D * Real.sqrt (-Real.log eps))
  have hmid : (∑' N : ℕ,
      if p + 2 ≤ N ∧ (N : ℝ) < D * Real.sqrt (-Real.log eps) then K N else 0) =
      intermediateOddKSNormWindow p d eta alpha tau j D eps cut := by
    apply tsum_congr
    intro N
    dsimp only [intermediateOddKSNormWindow, K]
    by_cases hc : p + 2 ≤ N ∧ (N : ℝ) < D * Real.sqrt (-Real.log eps)
    · have h2 : 2 ≤ N := by omega
      simp only [hc, h2, ite_true, f, r, s]
    · simp only [hc, ite_false]
  have hhigh : (∑' N : ℕ,
      if D * Real.sqrt (-Real.log eps) ≤ (N : ℝ) then K N else 0) =
      highKSNormTail d eta alpha tau j D eps cut := by
    apply tsum_congr
    intro N
    dsimp only [highKSNormTail, K]
    by_cases h2 : 2 ≤ N <;>
      by_cases ht : D * Real.sqrt (-Real.log eps) ≤ (N : ℝ) <;>
      simp only [h2, ht, true_and, false_and, ite_true, ite_false, f, r, s]
  rw [hmid, hhigh] at hKle
  dsimp only [F, L, f, r, s] at hsum hFle hLle
  linarith

end
end IsingBulk.HT.Tail
