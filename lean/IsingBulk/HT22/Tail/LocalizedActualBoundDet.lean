import IsingBulk.HT22.Tail.TotalFrameBounds
import IsingBulk.HT22.Tail.MixedRecursion

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A fixed finite determinant needs no sharp large-N estimate. This literal
Leibniz bound is used only for arbitrary fixed-N localized remainders. -/
theorem frameJet_det_bound {N M : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (K : ℂ → (Fin N → ℝ) → Matrix (Fin M) (Fin M) ℂ)
    (hK : ∀ i k,PreferredMixedSmoothOn (fun z => K z.1 z.2 i k) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j : ℕ) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ i k xs,xs.length≤j → ‖frameJet τ p m (fun t x => K t x i k) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m (fun t x => (K t x).det) xs s θ‖≤
      (1+∑ σ : Equiv.Perm (Fin M), ‖((Equiv.Perm.sign σ:ℤ):ℂ)‖)*(2^j*C)^M := by
  let P := fun (σ : Equiv.Perm (Fin M)) (t : ℂ) (x : Fin N → ℝ) => ∏ i,K t x (σ i) i
  let F := fun (σ : Equiv.Perm (Fin M)) (t : ℂ) (x : Fin N → ℝ) =>
    ((Equiv.Perm.sign σ:ℤ):ℂ)*P σ t x
  have hP (σ : Equiv.Perm (Fin M)) : PreferredMixedSmoothOn (fun z => P σ z.1 z.2) Ω := by
    intro z hz
    exact ⟨contDiffAt_prod (fun i _ => (hK (σ i) i z hz).1),
      DifferentiableAt.fun_finsetProd (fun i _ => (hK (σ i) i z hz).2)⟩
  have hF (σ : Equiv.Perm (Fin M)) : PreferredMixedSmoothOn (fun z => F σ z.1 z.2) Ω :=
    (PreferredMixedSmoothOn.const Ω _).mul (hP σ)
  have heq : (fun t x => (K t x).det)=(fun t x => ∑ σ,F σ t x) := by
    funext t x
    exact Matrix.det_apply' _
  rw [heq,frameJet_sum τ δ p m hp hm Ω hΩ hpoint hR F hF xs s θ hz]
  have hterm (σ : Equiv.Perm (Fin M)) :
      ‖frameJet τ p m (F σ) xs s θ‖≤‖((Equiv.Perm.sign σ:ℤ):ℂ)‖*(2^j*C)^M := by
    have hh := frameJet_list_prod_bound τ δ p m hp hm Ω hΩ hpoint hR
      (fun i t x => K t x (σ i) i) (Finset.univ.toList : List (Fin M))
      (fun i _ => hK (σ i) i) s θ hz j C hC (fun i _ => hbound (σ i) i) xs hxs
    simp only [Finset.prod_map_toList,Finset.length_toList,Finset.card_univ,Fintype.card_fin] at hh
    change ‖frameJet τ p m (fun t x => ((Equiv.Perm.sign σ:ℤ):ℂ)*P σ t x) xs s θ‖≤_
    rw [frameJet_const_mul τ δ p m hp hm Ω hΩ hpoint hR (P σ) (hP σ) _ xs s θ hz,norm_mul]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
  calc
    _ ≤ ∑ σ,‖frameJet τ p m (F σ) xs s θ‖ := norm_sum_le _ _
    _ ≤ ∑ σ,‖((Equiv.Perm.sign σ:ℤ):ℂ)‖*(2^j*C)^M := Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (∑ σ,‖((Equiv.Perm.sign σ:ℤ):ℂ)‖)*(2^j*C)^M := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)


theorem sourceBorderedKernel_entry_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (i k : Fin (N+1)) :
    PreferredMixedSmoothOn (fun z => sourceBorderedKernel τ p m z.1 z.2 i k) Ω := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact PreferredMixedSmoothOn.const Ω 0
    · exact PreferredMixedSmoothOn.const Ω 1
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact PreferredMixedSmoothOn.const Ω (-1)
    · exact sourceOrdinaryKernel_mixed τ δ p m hp hm Ω hpoint (i,k)

theorem sourceBorderedKernel_frame_bound {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (j : ℕ) (C : ℝ) (hC : 1≤C)
    (hK : ∀ i k xs,xs.length≤j →
      ‖frameJet τ p m (fun t x => sourceOrdinaryKernel τ p m t x i k) xs s θ‖≤C)
    (i k : Fin (N+1)) (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m (fun t x => sourceBorderedKernel τ p m t x i k) xs s θ‖≤C := by
  have hc (c : ℂ) (hc : ‖c‖≤1) : ‖frameJet τ p m (fun _ _ => c) xs s θ‖≤C := by
    rw [frameJet_const]
    split_ifs
    · exact hc.trans hC
    · simpa only [norm_zero] using (zero_le_one.trans hC)
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact hc 0 (by norm_num)
    · exact hc 1 (by norm_num)
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact hc (-1) (by norm_num)
    · exact hK i k xs hxs


theorem matrix_det_mixed {N M : ℕ} (Ω : Set (ℂ × (Fin N → ℝ)))
    (K : ℂ → (Fin N → ℝ) → Matrix (Fin M) (Fin M) ℂ)
    (hK : ∀ i k,PreferredMixedSmoothOn (fun z => K z.1 z.2 i k) Ω) :
    PreferredMixedSmoothOn (fun z => (K z.1 z.2).det) Ω := by
  intro z hz
  simp only [Matrix.det_apply']
  constructor
  · apply ContDiffAt.sum
    intro σ _
    exact contDiffAt_const.mul (contDiffAt_prod (fun i _ => (hK (σ i) i z hz).1))
  · apply DifferentiableAt.fun_sum
    intro σ _
    exact differentiableAt_const _ |>.mul (DifferentiableAt.fun_finsetProd (fun i _ => (hK (σ i) i z hz).2))

end
end IsingBulk.HT22.Tail
