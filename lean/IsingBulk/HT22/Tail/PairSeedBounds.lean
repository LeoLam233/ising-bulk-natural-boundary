import IsingBulk.HT22.Tail.FrameProducts
import IsingBulk.HT22.Tail.PairFactorization
import IsingBulk.Preferred22.VandermondeSeed

/-! Exact shared original pair scalar, bounded using the new fixed-v frames.
No old transport scalar or old frame endpoint is reused. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem pairAmplitude_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2) ≠ 0)
    (hQ : ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (k : ℕ) (C : ℝ) (hC : 1≤C)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖frameJet τ p m
      (fun t x => preferredVandermondeKernelAmplitude t (preferredSourceCoordinate τ p m t x)) xs s θ‖≤
      (2^k*((2^k*(2^k*C*C))^N))^N := by
  let Q := fun (i j : Fin N) (t : ℂ) (x : Fin N → ℝ) => preferredSourceKernelQuotient τ p m t x i j
  let C₂ := (2:ℝ)^k*C*C
  have hC₀ : 0≤C := le_trans (by norm_num) hC
  have htwo : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have hC₂ : 1≤C₂ := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le htwo hC) hC
  have hbase : 1≤(2:ℝ)^k*C₂ := one_le_mul_of_one_le_of_one_le htwo hC₂
  have hsq (i j : Fin N) : PreferredMixedSmoothOn (fun z => (Q i j z.1 z.2)^2) Ω := by
    simpa only [pow_two] using (hQ i j).mul (hQ i j)
  have hsquare (i j : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤k) :
      ‖frameJet τ p m (fun t x => (Q i j t x)^2) ys s θ‖≤C₂ := by
    simpa only [pow_two] using frameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint hR
      (Q i j) (Q i j) (hQ i j) (hQ i j) s θ hz k C C hC₀ hC₀ (hQj i j) (hQj i j) ys hys
  let R := fun (i : Fin N) (t : ℂ) (x : Fin N → ℝ) => ∏ j∈Finset.Ioi i, (Q i j t x)^2
  have hRm (i : Fin N) : PreferredMixedSmoothOn (fun z => R i z.1 z.2) Ω := by
    intro z hz
    exact ⟨contDiffAt_prod (fun j _ => (hsq i j z hz).1),
      DifferentiableAt.fun_finsetProd (fun j _ => (hsq i j z hz).2)⟩
  have hrow (i : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤k) :
      ‖frameJet τ p m (R i) ys s θ‖≤(2^k*C₂)^N := by
    have hh := frameJet_list_prod_bound τ δ p m hp hm Ω hΩ hpoint hR
      (fun j t x => (Q i j t x)^2) (Finset.Ioi i).toList (fun j _ => hsq i j) s θ hz k C₂
      (le_trans (by norm_num) hC₂) (fun j _ => hsquare i j) ys hys
    simp only [Finset.prod_map_toList,Finset.length_toList] at hh
    apply hh.trans
    apply pow_le_pow_right₀ hbase
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.Ioi i))
  have hh := frameJet_list_prod_bound τ δ p m hp hm Ω hΩ hpoint hR R
    (Finset.univ.toList : List (Fin N)) (fun i _ => hRm i) s θ hz k ((2^k*C₂)^N)
    (by positivity) (fun i _ => hrow i) xs hxs
  simpa only [Finset.prod_map_toList,Finset.length_toList,Finset.card_univ,Fintype.card_fin,
    R,Q,C₂,preferredVandermondeKernelAmplitude,preferredSourceKernelQuotient] using hh

/-- Only original seed jets and actual quotient jets enter this bound;
there is no loss of the physical factorial normalization. -/
theorem pairSeed_frame_bound {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2) ≠ 0)
    (hQ : ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (k : ℕ) (A C : ℝ) (hA : 0≤A) (hC : 1≤C)
    (hAj : ∀ xs, xs.length≤k →
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
        frameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤A)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
      frameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤
      2^k*A*(2^k*((2^k*(2^k*C*C))^N))^N := by
  let Z : ℂ := (N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)
  let F := preferredRegularSeedCoefficient τ η p m r (N:=N)
  let G := fun (t : ℂ) (x : Fin N → ℝ) => preferredVandermondeKernelAmplitude t (preferredSourceCoordinate τ p m t x)
  have hFm := preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint
  have hGm := preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQ
  have hFZ := (PreferredMixedSmoothOn.const Ω Z).mul hFm
  have hseedm := hFm.mul hGm
  have hZeq : (fun t x => Z*preferredVandermondeSeed τ η p m r t x)=
      (fun t x => (Z*F t x)*G t x) := by funext t x; dsimp [preferredVandermondeSeed,F,G]; ring
  change ‖Z*frameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤_
  rw [←frameJet_const_mul τ δ p m hp hm Ω hΩ hpoint hR _ hseedm Z xs s θ hz,hZeq]
  apply frameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint hR (fun t x => Z*F t x) G hFZ hGm
    s θ hz k A ((2^k*((2^k*(2^k*C*C))^N))^N) hA (by positivity) _ _ xs hxs
  · intro ys hys
    rw [frameJet_const_mul τ δ p m hp hm Ω hΩ hpoint hR F hFm Z ys s θ hz]
    exact hAj ys hys
  · intro ys hys
    exact pairAmplitude_frame_bound τ δ p m hp hm Ω hΩ hpoint hR hQ s θ hz k C hC hQj ys hys

end
end IsingBulk.HT22.Tail
