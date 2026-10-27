import IsingBulk.Preferred22.VandermondeTransport
import IsingBulk.Preferred22.FrameWeightedBounds

/-! Weighted all-word induction for the literal scalar recurrence after
the complete Vandermonde has been removed. Only jets of original factors
are hypotheses; no generated descendant bound is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def preferredVandermondePotential {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredRegularDivergenceCoefficient τ p m s θ+2*preferredUpperPairSum (C s θ)

theorem preferredVandermondeTransportStep_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    preferredVandermondeTransportStep τ p m C H s θ=
      preferredFrameStep τ p m none H s θ+
      (∑ a, preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) a*
        preferredFrameStep τ p m (some a) H s θ)+
      preferredVandermondePotential τ p m C s θ*H s θ := by
  unfold preferredVandermondeTransportStep preferredRegularTransportStep preferredVandermondePotential
    preferredRegularDivergenceCoefficient preferredFrameStep
  ring

theorem preferredFrameJet_step {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (a : Option (Fin N)) (xs : List (Option (Fin N))) :
    preferredFrameJet τ p m (preferredFrameStep τ p m a H) xs=
      preferredFrameJet τ p m H (xs++[a]) := by
  cases a with
  | none => exact preferredFrameJet_append τ p m H xs [none]
  | some a => exact preferredFrameJet_append τ p m H xs [some a]

theorem preferredVandermondePotential_mixed {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω) :
    PreferredMixedSmoothOn (fun z => preferredVandermondePotential τ p m C z.1 z.2) Ω := by
  have hd : PreferredMixedSmoothOn
      (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω := by
    change PreferredMixedSmoothOn (fun z => ∑ a : Fin N,
      preferredFrameStep τ p m (some a)
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) z.1 z.2) Ω
    exact PreferredMixedSmoothOn.sum (fun a : Fin N =>
      preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a)
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) (hB a))
  have hsum : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun k _ => (hC i k z hz).1),
      DifferentiableAt.fun_sum (fun k _ => (hC i k z hz).2)⟩
  exact hd.add ((PreferredMixedSmoothOn.const Ω 2).mul hsum)

theorem preferredVandermondePotential_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (B₀ C₀ d : ℝ) (_hB₀ : 0≤B₀) (hC₀ : 0≤C₀) (hd : 0<d)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+preferredCoordinateJetOrder xs))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => C t x i j) xs s θ‖≤
        C₀/d^(2+preferredCoordinateJetOrder xs))
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖preferredFrameJet τ p m (preferredVandermondePotential τ p m C) xs s θ‖≤
      ((N:ℝ)*B₀+2*(N:ℝ)^2*C₀)/d^(2+preferredCoordinateJetOrder xs) := by
  have hdm : PreferredMixedSmoothOn
      (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω := by
    change PreferredMixedSmoothOn (fun z => ∑ a : Fin N,
      preferredFrameStep τ p m (some a)
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) z.1 z.2) Ω
    exact PreferredMixedSmoothOn.sum (fun a : Fin N =>
      preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a)
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) (hB a))
  have hsm : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun j _ => (hC i j z hz).1),
      DifferentiableAt.fun_sum (fun j _ => (hC i j z hz).2)⟩
  have hdj : ‖preferredFrameJet τ p m (preferredRegularDivergenceCoefficient τ p m) xs s θ‖≤
      (N:ℝ)*B₀/d^(2+preferredCoordinateJetOrder xs) := by
    rw [show preferredRegularDivergenceCoefficient τ p m=(fun t x => ∑ a,
      preferredFrameStep τ p m (some a)
        (fun u y => preferredResidualCollective u (preferredSourceCoordinate τ p m u y) a) t x) by rfl]
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hpoint _
      (fun a => preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a) _ (hB a)) xs s θ hz]
    apply (norm_sum_le _ _).trans
    have hh : (∑ a : Fin N, ‖preferredFrameJet τ p m
        (preferredFrameStep τ p m (some a)
          (fun u y => preferredResidualCollective u (preferredSourceCoordinate τ p m u y) a)) xs s θ‖)≤
        ∑ _a : Fin N, B₀/d^(2+preferredCoordinateJetOrder xs) := by
      apply Finset.sum_le_sum
      intro a _
      rw [preferredFrameJet_step]
      have ha := hBj a (xs++[some a]) (by simpa using Nat.add_le_add_right hxs 1)
      have he : 1+preferredCoordinateJetOrder (xs++[some a])=2+preferredCoordinateJetOrder xs := by
        simp [preferredCoordinateJetOrder]
        omega
      simpa only [he] using ha
    exact hh.trans_eq (by simp; ring)
  have hsj : ‖preferredFrameJet τ p m (fun t x => preferredUpperPairSum (C t x)) xs s θ‖≤
      (N:ℝ)^2*C₀/d^(2+preferredCoordinateJetOrder xs) := by
    unfold preferredUpperPairSum
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hpoint _
      (fun i z hz => ⟨ContDiffAt.sum (fun j _ => (hC i j z hz).1),
        DifferentiableAt.fun_sum (fun j _ => (hC i j z hz).2)⟩) xs s θ hz]
    apply (norm_sum_le _ _).trans
    have hh : (∑ i : Fin N, ‖preferredFrameJet τ p m
        (fun t x => ∑ j∈Finset.Ioi i, C t x i j) xs s θ‖)≤
        ∑ _i : Fin N, (N:ℝ)*C₀/d^(2+preferredCoordinateJetOrder xs) := by
      apply Finset.sum_le_sum
      intro i _
      rw [preferredFrameJet_finset_sum τ δ p m hp hm Ω hΩ hpoint
        (fun j t x => C t x i j) (Finset.Ioi i) (fun j _ => hC i j) xs s θ hz]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _j∈Finset.Ioi i, C₀/d^(2+preferredCoordinateJetOrder xs) :=
          Finset.sum_le_sum (fun j _ => hCj i j xs hxs)
        _ = ((Finset.Ioi i).card:ℝ)*C₀/d^(2+preferredCoordinateJetOrder xs) := by simp; ring
        _ ≤ _ := by
          have hn : ((Finset.Ioi i).card:ℝ)≤N := by
            have hh : (Finset.Ioi i).card≤N := by
              simpa only [Finset.card_univ,Fintype.card_fin] using
                Finset.card_le_card (Finset.subset_univ (Finset.Ioi i))
            exact_mod_cast hh
          gcongr
    exact hh.trans_eq (by simp; ring)
  change ‖preferredFrameJet τ p m (fun t x =>
    preferredRegularDivergenceCoefficient τ p m t x+2*preferredUpperPairSum (C t x)) xs s θ‖≤_
  rw [preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint _ _ hdm
      ((PreferredMixedSmoothOn.const Ω 2).mul hsm) xs s θ hz,
    preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hpoint _ hsm 2 xs s θ hz]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  rw [Complex.norm_two]
  calc
    _ ≤ (N:ℝ)*B₀/d^(2+preferredCoordinateJetOrder xs)+
        2*((N:ℝ)^2*C₀/d^(2+preferredCoordinateJetOrder xs)) :=
      add_le_add hdj (mul_le_mul_of_nonneg_left hsj (by norm_num))
    _ = _ := by ring

theorem preferredVandermondeScalar_mixed_frames {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => preferredVandermondeScalar τ p m C A j z.1 z.2) Ω := by
  have hP := preferredVandermondePotential_mixed τ δ p m hp hm C Ω hΩ hpoint hB hC
  induction j with
  | zero => exact hA
  | succ j ih =>
    have hEs := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint none _ ih
    have hTr := PreferredMixedSmoothOn.sum (fun a => (hB a).mul
      (preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a) _ ih))
    apply ((hEs.add hTr).add (hP.mul ih)).congr hΩ
    intro z _
    exact (preferredVandermondeTransportStep_eq τ p m C _ z.1 z.2).symm

theorem preferredVandermondeTransportStep_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω)
    (hP : PreferredMixedSmoothOn (fun z => preferredVandermondePotential τ p m C z.1 z.2) Ω)
    (hH : PreferredMixedSmoothOn (fun z => H z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (J h : ℕ) (A B₀ P₀ d D : ℝ) (hA : 0≤A) (hB₀ : 0≤B₀) (hP₀ : 0≤P₀)
    (hd : 0<d) (hdD : d≤D)
    (hBj : ∀ a xs, xs.length≤J →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+preferredCoordinateJetOrder xs))
    (hPj : ∀ xs, xs.length≤J →
      ‖preferredFrameJet τ p m (preferredVandermondePotential τ p m C) xs s θ‖≤
        P₀/d^(2+preferredCoordinateJetOrder xs))
    (hHj : ∀ xs, xs.length≤J+1 →
      ‖preferredFrameJet τ p m H xs s θ‖≤A/d^(h+preferredCoordinateJetOrder xs))
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) :
    ‖preferredFrameJet τ p m (preferredVandermondeTransportStep τ p m C H) xs s θ‖≤
      A*(D^2+2^J*((N:ℝ)*B₀+P₀))/d^(h+2+preferredCoordinateJetOrder xs) := by
  let B := fun (a : Fin N) (t : ℂ) (x : Fin N → ℝ) =>
    preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a
  let P := preferredVandermondePotential τ p m C
  have hEs := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint none H hH
  have hEa (a : Fin N) := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a) H hH
  have hsmooth := PreferredMixedSmoothOn.sum (fun a => (hB a).mul (hEa a))
  have hpar : ‖preferredFrameJet τ p m (preferredFrameStep τ p m none H) xs s θ‖≤
      A*D^2/d^(h+2+preferredCoordinateJetOrder xs) := by
    rw [preferredFrameJet_step]
    have hh := hHj (xs++[none]) (by simpa using Nat.add_le_add_right hxs 1)
    have hnone : preferredCoordinateJetOrder (xs++[none])=preferredCoordinateJetOrder xs := by
      simp [preferredCoordinateJetOrder]
    rw [hnone] at hh
    apply hh.trans
    have hr := mul_le_mul_of_nonneg_left
      (inverse_power_raise d D hd hdD (h+preferredCoordinateJetOrder xs) 2) hA
    have he : h+preferredCoordinateJetOrder xs+2=h+2+preferredCoordinateJetOrder xs := by omega
    simpa only [←mul_div_assoc,mul_one,he] using hr
  have hcoord (a : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ p m (preferredFrameStep τ p m (some a) H) ys s θ‖≤
        A/d^((h+1)+preferredCoordinateJetOrder ys) := by
    rw [preferredFrameJet_step]
    have hh := hHj (ys++[some a]) (by simpa using Nat.add_le_add_right hys 1)
    have hsome : preferredCoordinateJetOrder (ys++[some a])=preferredCoordinateJetOrder ys+1 := by
      simp [preferredCoordinateJetOrder]
    rw [hsome] at hh
    convert hh using 1
    congr 2
    omega
  have hterm (a : Fin N) :
      ‖preferredFrameJet τ p m (fun t x => B a t x*preferredFrameStep τ p m (some a) H t x) xs s θ‖≤
        2^J*B₀*A/d^(h+2+preferredCoordinateJetOrder xs) := by
    have hh := preferredFrameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hpoint
      (B a) (preferredFrameStep τ p m (some a) H) (hB a) (hEa a) s θ hz
      J 1 (h+1) B₀ A d hB₀ hA hd (hBj a) (hcoord a) xs hxs
    convert hh using 1
    congr 2
    omega
  have htr : ‖preferredFrameJet τ p m (fun t x =>
      ∑ a, B a t x*preferredFrameStep τ p m (some a) H t x) xs s θ‖≤
      (N:ℝ)*2^J*B₀*A/d^(h+2+preferredCoordinateJetOrder xs) := by
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hpoint _
      (fun a => (hB a).mul (hEa a)) xs s θ hz]
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (fun a _ => hterm a)).trans_eq (by simp; ring)
  have hpot : ‖preferredFrameJet τ p m (fun t x => P t x*H t x) xs s θ‖≤
      2^J*P₀*A/d^(h+2+preferredCoordinateJetOrder xs) := by
    have hh := preferredFrameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hpoint P H hP hH s θ hz
      J 2 h P₀ A d hP₀ hA hd hPj (fun ys hys => hHj ys (by omega)) xs hxs
    convert hh using 1
    congr 2
    omega
  have he : preferredVandermondeTransportStep τ p m C H=(fun t x =>
      preferredFrameStep τ p m none H t x+
      (∑ a, B a t x*preferredFrameStep τ p m (some a) H t x)+P t x*H t x) := by
    funext t x
    exact preferredVandermondeTransportStep_eq τ p m C H t x
  rw [he,preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint _ _ (hEs.add hsmooth) (hP.mul hH) xs s θ hz,
    preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint _ _ hEs hsmooth xs s θ hz]
  apply (norm_add_le _ _).trans
  have hn := norm_add_le
    (preferredFrameJet τ p m (preferredFrameStep τ p m none H) xs s θ)
    (preferredFrameJet τ p m (fun t x => ∑ a, B a t x*preferredFrameStep τ p m (some a) H t x) xs s θ)
  calc
    _ ≤ (‖preferredFrameJet τ p m (preferredFrameStep τ p m none H) xs s θ‖+
        ‖preferredFrameJet τ p m (fun t x => ∑ a, B a t x*preferredFrameStep τ p m (some a) H t x) xs s θ‖)+
        ‖preferredFrameJet τ p m (fun t x => P t x*H t x) xs s θ‖ :=
      add_le_add hn le_rfl
    _ ≤ (A*D^2/d^(h+2+preferredCoordinateJetOrder xs)+
        (N:ℝ)*2^J*B₀*A/d^(h+2+preferredCoordinateJetOrder xs))+
        2^J*P₀*A/d^(h+2+preferredCoordinateJetOrder xs) :=
      add_le_add (add_le_add hpar htr) hpot
    _ = _ := by ring

/-- Joint induction on transport order and remaining frame words. The
complete loss is exactly twice the transport order plus the coordinate
word count. The hypotheses concern only original seed/B/C factors. -/
theorem preferredVandermondeScalar_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (A₀ B₀ C₀ d D : ℝ) (hA₀ : 0≤A₀) (hB₀ : 0≤B₀) (hC₀ : 0≤C₀)
    (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hAj : ∀ xs, xs.length≤k → ‖preferredFrameJet τ p m A xs s θ‖≤A₀)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+preferredCoordinateJetOrder xs))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => C t x i j) xs s θ‖≤
        C₀/d^(2+preferredCoordinateJetOrder xs)) :
    ∀ j : ℕ, j≤k → ∀ xs : List (Option (Fin N)), xs.length+j≤k →
    ‖preferredFrameJet τ p m (preferredVandermondeScalar τ p m C A j) xs s θ‖≤
      (A₀*D^k)*(D^2+2^k*(2*(N:ℝ)*B₀+2*(N:ℝ)^2*C₀))^j/
        d^(2*j+preferredCoordinateJetOrder xs) := by
  let P₀ := (N:ℝ)*B₀+2*(N:ℝ)^2*C₀
  let S := D^2+2^k*((N:ℝ)*B₀+P₀)
  have hP₀ : 0≤P₀ := by dsimp [P₀]; positivity
  have hD₀ : 0≤D := le_trans (by norm_num) hD
  have hS : 0≤S := by dsimp [S]; positivity
  have hPm := preferredVandermondePotential_mixed τ δ p m hp hm C Ω hΩ hpoint hB hC
  have hPj := preferredVandermondePotential_frame_bound τ δ p m hp hm C Ω hΩ hpoint hB hC
    s θ hz k B₀ C₀ d hB₀ hC₀ hd hBj hCj
  have heS : S=D^2+2^k*(2*(N:ℝ)*B₀+2*(N:ℝ)^2*C₀) := by dsimp [S,P₀]; ring
  rw [←heS]
  intro j
  induction j with
  | zero =>
    intro _ xs hxs
    simpa [preferredVandermondeScalar] using preferredFrameJet_bounded_to_weighted τ p m A s θ
      k A₀ d D hA₀ hd hdD hD hAj xs (by omega)
  | succ j ih =>
    intro hjk xs hxs
    let remaining := k-(j+1)
    have hmj : remaining≤k := Nat.sub_le _ _
    have hxs' : xs.length≤remaining := by dsimp [remaining]; omega
    have hHj (ys : List (Option (Fin N))) (hys : ys.length≤remaining+1) :
        ‖preferredFrameJet τ p m (preferredVandermondeScalar τ p m C A j) ys s θ‖≤
          ((A₀*D^k)*S^j)/d^(2*j+preferredCoordinateJetOrder ys) := by
      apply ih (by omega) ys
      dsimp [remaining] at hys
      omega
    have hh := preferredVandermondeTransportStep_frame_bound τ δ p m hp hm C
      (preferredVandermondeScalar τ p m C A j) Ω hΩ hpoint hB hPm
      (preferredVandermondeScalar_mixed_frames τ δ p m hp hm C A Ω hΩ hpoint hB hC hA j)
      s θ hz remaining (2*j) ((A₀*D^k)*S^j) B₀ P₀ d D (by positivity) hB₀ hP₀ hd hdD
      (fun a ys hys => hBj a ys (by omega))
      (fun ys hys => hPj ys (hys.trans hmj)) hHj xs hxs'
    have hfactor : D^2+2^remaining*((N:ℝ)*B₀+P₀)≤S := by
      dsimp only [S]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hmj)
        (by positivity : 0≤(N:ℝ)*B₀+P₀))
    change ‖preferredFrameJet τ p m
      (preferredVandermondeTransportStep τ p m C (preferredVandermondeScalar τ p m C A j)) xs s θ‖≤_
    calc
      _ ≤ ((A₀*D^k)*S^j)*(D^2+2^remaining*((N:ℝ)*B₀+P₀))/d^(2*j+2+preferredCoordinateJetOrder xs) := hh
      _ ≤ ((A₀*D^k)*S^j)*S/d^(2*j+2+preferredCoordinateJetOrder xs) := by
        gcongr
      _ = (A₀*D^k)*S^(j+1)/d^(2*(j+1)+preferredCoordinateJetOrder xs) := by
        rw [pow_succ]
        congr 1
        ring

end
end IsingBulk.Preferred22
