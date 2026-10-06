import IsingBulk.Tail.SelectorOrderSplit
import IsingBulk.Tail.UpperExteriorSeries
import IsingBulk.Tail.HighKSTail

/-! Stronger all-order source domination. Unlike the manuscript's upper
window split, this internal route uses the proved full F/largeS series.
UltraHigh remains a separately proved source node, not a dummy premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped Topology
set_option maxHeartbeats 1200000

theorem nonnegative_subsequence_window_split (v : ℕ → ℝ) (hv : ∀ N, 0 ≤ v N)
    (hs : Summable v) (p : ℕ) (T : ℝ) :
    (∑' n : ℕ, v (2*(n+p+1))) ≤
      (∑' N : ℕ, if 2*(p+1)≤N ∧ (N:ℝ)<T then v N else 0) +
      (∑' N : ℕ, if T≤(N:ℝ) then v N else 0) := by
  let low := fun N : ℕ => if 2*(p+1)≤N then v N else 0
  let mid := fun N : ℕ => if 2*(p+1)≤N ∧ (N:ℝ)<T then v N else 0
  let high := fun N : ℕ => if T≤(N:ℝ) then v N else 0
  have hlow : Summable low := hs.of_nonneg_of_le
    (fun N => by dsimp [low]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [low]; split_ifs <;> simp [hv N])
  have hmid : Summable mid := hs.of_nonneg_of_le
    (fun N => by dsimp [mid]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [mid]; split_ifs <;> simp [hv N])
  have hhigh : Summable high := hs.of_nonneg_of_le
    (fun N => by dsimp [high]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [high]; split_ifs <;> simp [hv N])
  have hinj : Function.Injective (fun n : ℕ => 2*(n+p+1)) := by intro a b h; dsimp at h; omega
  have hfirst : (∑' n : ℕ, v (2*(n+p+1))) ≤ ∑' N, low N :=
    (hs.comp_injective hinj).tsum_le_tsum_of_inj _ hinj
      (fun N _ => by dsimp [low]; split_ifs <;> simp [hv N])
      (fun n => by dsimp [low]; rw [ite_eq_left (by omega)]) hlow
  have hpoint (N : ℕ) : low N ≤ mid N+high N := by
    by_cases hL : 2*(p+1)≤N
    · by_cases hT : (N:ℝ)<T
      · simp [low,mid,high,hL,hT,not_le.mpr hT]
      · simp [low,mid,high,hL,hT,le_of_not_gt hT]
    · dsimp [low,mid,high]
      simp only [hL,false_and,ite_false,zero_add]
      split_ifs <;> simp [hv N]
  exact hfirst.trans ((Summable.tsum_le_tsum hpoint hlow (hmid.add hhigh)).trans_eq
    (hmid.tsum_add hhigh))

def intermediateKSNormWindow (p : ℕ) (d : LocalBranchData) (eta alpha tau : ℝ)
    (j : ℕ) (D eps cut : ℝ) : ℝ :=
  ∑' N : ℕ, if 2*(p+1)≤N ∧ (N:ℝ)<D*Real.sqrt (-Real.log eps) then
    originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
      (radialParameter d.theta eps) cut else 0

theorem actual_higher_tail_domination (p : ℕ) (d : LocalBranchData) (eta alpha tau D eps cut : ℝ)
    (hf : RegularSelector (constructedSelector d.thetaB eta alpha)) (htau : 0 ≤ tau)
    (heps : 0 < eps) (hcut : cut ∈ Icc (0:ℝ) 1)
    (hs : radialParameter d.theta eps ∈ dampingDomain (Real.exp (-d.c₀*eps))) (j : ℕ)
    (hF : Summable (fun n : ℕ => ‖iteratedDeriv j
      (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau)
      (radialParameter d.theta eps)‖))
    (hL : Summable (fun n : ℕ => ‖∫ lam in cut..1,
      differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀*eps)) tau lam j (radialParameter d.theta eps)‖))
    (hK : Summable (fun N : ℕ => if 2≤N then
      originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
        (radialParameter d.theta eps) cut else 0)) :
    (∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(n+p+1))) (radialParameter d.theta eps)‖) ≤
      (∑' n : ℕ, ‖iteratedDeriv j
        (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau)
        (radialParameter d.theta eps)‖) +
      (∑' n : ℕ, ‖∫ lam in cut..1,
        differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) tau lam j (radialParameter d.theta eps)‖) +
      intermediateKSNormWindow p d eta alpha tau j D eps cut + highKSNormTail d eta alpha tau j D eps cut := by
  let f := constructedSelector d.thetaB eta alpha
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := fun n : ℕ => ‖iteratedDeriv j (selectedIntegral (2*(n+1)) f r tau) s‖
  let L := fun n : ℕ => ‖∫ lam in cut..1, differentiatedCurrentSlice (2*(n+1)) f r tau lam j s‖
  let K := fun N : ℕ => if 2≤N then originalKSNorm N f r tau j s cut else 0
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have htrace : 0 < (sourceS (radialParameter d.theta eps)).im := by
    have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
    have hm := hs.2
    change r⁻¹-r < _ at hm
    linarith
  have hu := (upperEven_derivative_summable j htrace).comp_injective
    (show Function.Injective (fun n : ℕ => n+p) from fun a b h => Nat.add_right_cancel h)
  have hinj : Function.Injective (fun n : ℕ => 2*(n+p+1)) := by intro a b h; dsimp at h; omega
  have hFs : Summable (fun n : ℕ => F (n+p)) := hF.comp_injective (show Function.Injective (fun n : ℕ => n+p) from fun a b h => Nat.add_right_cancel h)
  have hLs : Summable (fun n : ℕ => L (n+p)) := hL.comp_injective (show Function.Injective (fun n : ℕ => n+p) from fun a b h => Nat.add_right_cancel h)
  have hKs : Summable (fun n : ℕ => K (2*(n+p+1))) := hK.comp_injective hinj
  have hpoint (n : ℕ) : ‖iteratedDeriv j (upperFormFactor (2*(n+p+1))) s‖ ≤
      F (n+p)+K (2*(n+p+1))+L (n+p) := by
    dsimp [F,K,L]
    exact selector_derivative_norm_split _ (by omega) f hf hr hr1 htau hcut hs j
  have hsum := Summable.tsum_le_tsum hpoint hu ((hFs.add hKs).add hLs)
  rw [(hFs.add hKs).tsum_add hLs,hFs.tsum_add hKs] at hsum
  have hFle : (∑' n : ℕ, F (n+p)) ≤ ∑' n : ℕ, F n :=
    hFs.tsum_le_tsum_of_inj (fun n => n+p) (fun a b h => Nat.add_right_cancel h)
      (fun n _ => norm_nonneg _) (fun _ => le_rfl) hF
  have hLle : (∑' n : ℕ, L (n+p)) ≤ ∑' n : ℕ, L n :=
    hLs.tsum_le_tsum_of_inj (fun n => n+p) (fun a b h => Nat.add_right_cancel h)
      (fun n _ => norm_nonneg _) (fun _ => le_rfl) hL
  have hK0 (N : ℕ) : 0≤K N := by dsimp [K]; split_ifs; exact originalKSNorm_nonneg _ _ _ _ _ _ _; exact le_rfl
  have hKle := nonnegative_subsequence_window_split K hK0 hK p (D*Real.sqrt (-Real.log eps))
  have hmid : (∑' N : ℕ, if 2*(p+1)≤N ∧ (N:ℝ)<D*Real.sqrt (-Real.log eps) then K N else 0) =
      intermediateKSNormWindow p d eta alpha tau j D eps cut := by
    apply tsum_congr
    intro N
    dsimp only [intermediateKSNormWindow,K]
    by_cases hc : 2*(p+1)≤N ∧ (N:ℝ)<D*Real.sqrt (-Real.log eps)
    · have h2 : 2≤N := by omega
      simp only [hc,h2,ite_true,f,r,s]
    · simp only [hc,ite_false]
  have hhigh : (∑' N : ℕ, if D*Real.sqrt (-Real.log eps)≤(N:ℝ) then K N else 0)=
      highKSNormTail d eta alpha tau j D eps cut := by
    apply tsum_congr
    intro N
    dsimp only [highKSNormTail,K]
    by_cases h2 : 2≤N <;> by_cases ht : D*Real.sqrt (-Real.log eps)≤(N:ℝ) <;>
      simp only [h2,ht,true_and,false_and,ite_true,ite_false,f,r,s]
  rw [hmid,hhigh] at hKle
  dsimp only [F,L,f,r,s] at hsum hFle hLle
  linarith

end
end IsingBulk.Tail
