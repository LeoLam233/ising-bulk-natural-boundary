import IsingBulk.Preferred22.RegularKernelQuotient
import IsingBulk.Preferred22.FrameWeightedBounds

/-! Exact full-Vandermonde seed and its original-factor frame bounds.
The factorial normalization is kept literal. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def preferredSourceKernelQuotient {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N) : ℂ :=
  preferredKernelQuotient s (preferredSourceCoordinate τ p m s θ i)
    (preferredSourceCoordinate τ p m s θ j)

def preferredVandermondeSeed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredRegularSeedCoefficient τ η p m r s θ*
    preferredVandermondeKernelAmplitude s (preferredSourceCoordinate τ p m s θ)

theorem preferredRegularSeed_vandermonde (n : ℕ) (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin (2*n) → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j)) :
    preferredRegularSeed τ η p m r s θ=
      preferredVandermondeSeed τ η p m r s θ*
        preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  rw [preferredRegularSeed_eq_empty_minor]
  simp only [preferredMarkedMinor,List.length_nil,iteratedFDeriv_zero_apply]
  rw [preferredSourceRegularKernel,preferredRegularKernel_vandermonde n c s _ hgood
    hpoint.phase_inside hpoint.phase_im_neg]
  unfold preferredVandermondeSeed
  ring

theorem preferredSourceKernelQuotient_mixed_of_good {N : ℕ}
    (τ δ c : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hgood : ∀ z∈Ω, ∀ i j, PreferredRightRegularPoint c z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j)) :
    ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω := by
  intro i j
  apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
    (fun z : ℂ × (Fin N → ℂ) => preferredKernelQuotient z.1 (z.2 i) (z.2 j))
  intro z hz
  have hqr := hgood z hz i j
  have hrr := hgood z hz j j
  have hQa := preferredKernelQuotient_analyticAt z.1
    (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j)
    (preferredKernelExtension_analyticAt _ _ _ hqr.2.1 hqr.2.2.1 hqr.1 hqr.2.2.2.2.2.2.2.2.2)
    (preferredKernelExtension_analyticAt _ _ _ hrr.2.1 hrr.2.2.1 hrr.1 hrr.2.2.2.2.2.2.2.2.2)
  exact AnalyticAt.comp
    (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i,x.2 j))
    (g := fun x : ℂ × ℂ × ℂ => preferredKernelQuotient x.1 x.2.1 x.2.2)
    hQa ((preferredPairProjection i j).analyticAt _)

theorem preferredVandermondeKernelAmplitude_source_mixed {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hQ : ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω) :
    PreferredMixedSmoothOn (fun z =>
      preferredVandermondeKernelAmplitude z.1 (preferredSourceCoordinate τ p m z.1 z.2)) Ω := by
  intro z hz
  have hq (i j : Fin N) := (hQ i j).mul (hQ i j) z hz
  constructor
  · apply contDiffAt_prod
    intro i _
    apply contDiffAt_prod
    intro j _
    simpa only [pow_two,preferredSourceKernelQuotient] using (hq i j).1
  · apply DifferentiableAt.fun_finsetProd
    intro i _
    apply DifferentiableAt.fun_finsetProd
    intro j _
    simpa only [pow_two,preferredSourceKernelQuotient] using (hq i j).2

theorem preferredVandermondeKernelAmplitude_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hQ : ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (k : ℕ) (C : ℝ) (hC : 1≤C)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖preferredFrameJet τ p m
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
      ‖preferredFrameJet τ p m (fun t x => (Q i j t x)^2) ys s θ‖≤C₂ := by
    simpa only [pow_two] using preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint
      (Q i j) (Q i j) (hQ i j) (hQ i j) s θ hz k C C hC₀ hC₀ (hQj i j) (hQj i j) ys hys
  let R := fun (i : Fin N) (t : ℂ) (x : Fin N → ℝ) => ∏ j∈Finset.Ioi i, (Q i j t x)^2
  have hRm (i : Fin N) : PreferredMixedSmoothOn (fun z => R i z.1 z.2) Ω := by
    intro z hz
    exact ⟨contDiffAt_prod (fun j _ => (hsq i j z hz).1),
      DifferentiableAt.fun_finsetProd (fun j _ => (hsq i j z hz).2)⟩
  have hrow (i : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤k) :
      ‖preferredFrameJet τ p m (R i) ys s θ‖≤(2^k*C₂)^N := by
    have hh := preferredFrameJet_list_prod_bound τ δ p m hp hm Ω hΩ hpoint
      (fun j t x => (Q i j t x)^2) (Finset.Ioi i).toList (fun j _ => hsq i j) s θ hz k C₂
      (le_trans (by norm_num) hC₂) (fun j _ => hsquare i j) ys hys
    simp only [Finset.prod_map_toList,Finset.length_toList] at hh
    apply hh.trans
    apply pow_le_pow_right₀ hbase
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.Ioi i))
  have hh := preferredFrameJet_list_prod_bound τ δ p m hp hm Ω hΩ hpoint R
    (Finset.univ.toList : List (Fin N)) (fun i _ => hRm i) s θ hz k ((2^k*C₂)^N)
    (by positivity) (fun i _ => hrow i) xs hxs
  simpa only [Finset.prod_map_toList,Finset.length_toList,Finset.card_univ,Fintype.card_fin,
    R,Q,C₂,preferredVandermondeKernelAmplitude,preferredSourceKernelQuotient] using hh

/-- Only original seed jets and actual quotient jets enter this bound;
there is no loss of the physical factorial normalization. -/
theorem preferredVandermondeSeed_frame_bound {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hQ : ∀ i j, PreferredMixedSmoothOn
      (fun z => preferredSourceKernelQuotient τ p m z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (k : ℕ) (A C : ℝ) (hA : 0≤A) (hC : 1≤C)
    (hAj : ∀ xs, xs.length≤k →
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
        preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤A)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
      preferredFrameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤
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
  change ‖Z*preferredFrameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤_
  rw [←preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hpoint _ hseedm Z xs s θ hz,hZeq]
  apply preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint (fun t x => Z*F t x) G hFZ hGm
    s θ hz k A ((2^k*((2^k*(2^k*C*C))^N))^N) hA (by positivity) _ _ xs hxs
  · intro ys hys
    rw [preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hpoint F hFm Z ys s θ hz]
    exact hAj ys hys
  · intro ys hys
    exact preferredVandermondeKernelAmplitude_frame_bound τ δ p m hp hm Ω hΩ hpoint hQ s θ hz k C hC hQj ys hys

end
end IsingBulk.Preferred22
