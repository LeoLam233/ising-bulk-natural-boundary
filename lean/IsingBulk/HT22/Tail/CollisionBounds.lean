import IsingBulk.HT22.Tail.CollisionRecurrence
import IsingBulk.HT22.Tail.TotalFrameBounds

/-! Total-joint-order near-collision induction. Every parameter derivative
of the new mixed field is charged, while each transport loses at most two
of the N(N−1) retained collision degrees. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def vandermondePotential {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  regularDivergence τ p m s θ+2*preferredUpperPairSum (C s θ)

theorem vandermondeTransportStep_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    vandermondeTransportStep τ p m C H s θ=
      frameStep τ p m none H s θ+
      (∑ a, residualField s (sourceCoordinate τ p m s θ) a*
        frameStep τ p m (some a) H s θ)+
      vandermondePotential τ p m C s θ*H s θ := by
  unfold vandermondeTransportStep regularTransportStep vandermondePotential
    regularDivergence frameStep
  ring

theorem frameJet_step {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (a : Option (Fin N)) (xs : List (Option (Fin N))) :
    frameJet τ p m (frameStep τ p m a H) xs=
      frameJet τ p m H (xs++[a]) := by
  cases a with
  | none => exact frameJet_append τ p m H xs [none]
  | some a => exact frameJet_append τ p m H xs [some a]

theorem vandermondePotential_mixed {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω) :
    PreferredMixedSmoothOn (fun z => vandermondePotential τ p m C z.1 z.2) Ω := by
  have hd : PreferredMixedSmoothOn
      (fun z => regularDivergence τ p m z.1 z.2) Ω := by
    change PreferredMixedSmoothOn (fun z => ∑ a : Fin N,
      frameStep τ p m (some a)
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) z.1 z.2) Ω
    exact PreferredMixedSmoothOn.sum (fun a : Fin N =>
      frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR (some a)
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) (hB a))
  have hsum : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun k _ => (hC i k z hz).1),
      DifferentiableAt.fun_sum (fun k _ => (hC i k z hz).2)⟩
  exact hd.add ((PreferredMixedSmoothOn.const Ω 2).mul hsum)

theorem vandermondePotential_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (B₀ C₀ d : ℝ) (_hB₀ : 0≤B₀) (hC₀ : 0≤C₀) (hd : 0<d)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+xs.length))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => C t x i j) xs s θ‖≤
        C₀/d^(2+xs.length))
    (xs : List (Option (Fin N))) (hxs : xs.length≤k) :
    ‖frameJet τ p m (vandermondePotential τ p m C) xs s θ‖≤
      ((N:ℝ)*B₀+2*(N:ℝ)^2*C₀)/d^(2+xs.length) := by
  have hdm : PreferredMixedSmoothOn
      (fun z => regularDivergence τ p m z.1 z.2) Ω := by
    change PreferredMixedSmoothOn (fun z => ∑ a : Fin N,
      frameStep τ p m (some a)
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) z.1 z.2) Ω
    exact PreferredMixedSmoothOn.sum (fun a : Fin N =>
      frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR (some a)
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) (hB a))
  have hsm : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun j _ => (hC i j z hz).1),
      DifferentiableAt.fun_sum (fun j _ => (hC i j z hz).2)⟩
  have hdj : ‖frameJet τ p m (regularDivergence τ p m) xs s θ‖≤
      (N:ℝ)*B₀/d^(2+xs.length) := by
    rw [show regularDivergence τ p m=(fun t x => ∑ a,
      frameStep τ p m (some a)
        (fun u y => residualField u (sourceCoordinate τ p m u y) a) t x) by rfl]
    rw [frameJet_sum τ δ p m hp hm Ω hΩ hpoint hR _
      (fun a => frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR (some a) _ (hB a)) xs s θ hz]
    apply (norm_sum_le _ _).trans
    have hh : (∑ a : Fin N, ‖frameJet τ p m
        (frameStep τ p m (some a)
          (fun u y => residualField u (sourceCoordinate τ p m u y) a)) xs s θ‖)≤
        ∑ _a : Fin N, B₀/d^(2+xs.length) := by
      apply Finset.sum_le_sum
      intro a _
      rw [frameJet_step]
      have ha := hBj a (xs++[some a]) (by simpa using Nat.add_le_add_right hxs 1)
      have he : 1+(xs++[some a]).length=2+xs.length := by
        simp
        omega
      simpa only [he] using ha
    exact hh.trans_eq (by simp; ring)
  have hsj : ‖frameJet τ p m (fun t x => preferredUpperPairSum (C t x)) xs s θ‖≤
      (N:ℝ)^2*C₀/d^(2+xs.length) := by
    unfold preferredUpperPairSum
    rw [frameJet_sum τ δ p m hp hm Ω hΩ hpoint hR _
      (fun i z hz => ⟨ContDiffAt.sum (fun j _ => (hC i j z hz).1),
        DifferentiableAt.fun_sum (fun j _ => (hC i j z hz).2)⟩) xs s θ hz]
    apply (norm_sum_le _ _).trans
    have hh : (∑ i : Fin N, ‖frameJet τ p m
        (fun t x => ∑ j∈Finset.Ioi i, C t x i j) xs s θ‖)≤
        ∑ _i : Fin N, (N:ℝ)*C₀/d^(2+xs.length) := by
      apply Finset.sum_le_sum
      intro i _
      rw [frameJet_finset_sum τ δ p m hp hm Ω hΩ hpoint hR
        (fun j t x => C t x i j) (Finset.Ioi i) (fun j _ => hC i j) xs s θ hz]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _j∈Finset.Ioi i, C₀/d^(2+xs.length) :=
          Finset.sum_le_sum (fun j _ => hCj i j xs hxs)
        _ = ((Finset.Ioi i).card:ℝ)*C₀/d^(2+xs.length) := by simp; ring
        _ ≤ _ := by
          have hn : ((Finset.Ioi i).card:ℝ)≤N := by
            have hh : (Finset.Ioi i).card≤N := by
              simpa only [Finset.card_univ,Fintype.card_fin] using
                Finset.card_le_card (Finset.subset_univ (Finset.Ioi i))
            exact_mod_cast hh
          gcongr
    exact hh.trans_eq (by simp; ring)
  change ‖frameJet τ p m (fun t x =>
    regularDivergence τ p m t x+2*preferredUpperPairSum (C t x)) xs s θ‖≤_
  rw [frameJet_add τ δ p m hp hm Ω hΩ hpoint hR _ _ hdm
      ((PreferredMixedSmoothOn.const Ω 2).mul hsm) xs s θ hz,
    frameJet_const_mul τ δ p m hp hm Ω hΩ hpoint hR _ hsm 2 xs s θ hz]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  rw [Complex.norm_two]
  calc
    _ ≤ (N:ℝ)*B₀/d^(2+xs.length)+
        2*((N:ℝ)^2*C₀/d^(2+xs.length)) :=
      add_le_add hdj (mul_le_mul_of_nonneg_left hsj (by norm_num))
    _ = _ := by ring

theorem vandermondeScalar_mixed_frames {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => vandermondeScalar τ p m C A j z.1 z.2) Ω := by
  have hP := vandermondePotential_mixed τ δ p m hp hm C Ω hΩ hpoint hR hB hC
  induction j with
  | zero => exact hA
  | succ j ih =>
    have hEs := frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR none _ ih
    have hTr := PreferredMixedSmoothOn.sum (fun a => (hB a).mul
      (frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR (some a) _ ih))
    apply ((hEs.add hTr).add (hP.mul ih)).congr hΩ
    intro z _
    exact (vandermondeTransportStep_eq τ p m C _ z.1 z.2).symm

theorem vandermondeTransportStep_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hP : PreferredMixedSmoothOn (fun z => vandermondePotential τ p m C z.1 z.2) Ω)
    (hH : PreferredMixedSmoothOn (fun z => H z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (J h : ℕ) (A B₀ P₀ d D : ℝ) (hA : 0≤A) (hB₀ : 0≤B₀) (hP₀ : 0≤P₀)
    (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hBj : ∀ a xs, xs.length≤J →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+xs.length))
    (hPj : ∀ xs, xs.length≤J →
      ‖frameJet τ p m (vandermondePotential τ p m C) xs s θ‖≤
        P₀/d^(2+xs.length))
    (hHj : ∀ xs, xs.length≤J+1 →
      ‖frameJet τ p m H xs s θ‖≤A/d^(h+xs.length))
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) :
    ‖frameJet τ p m (vandermondeTransportStep τ p m C H) xs s θ‖≤
      A*(D^2+2^J*((N:ℝ)*B₀+P₀))/d^(h+2+xs.length) := by
  let B := fun (a : Fin N) (t : ℂ) (x : Fin N → ℝ) =>
    residualField t (sourceCoordinate τ p m t x) a
  let P := vandermondePotential τ p m C
  have hEs := frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR none H hH
  have hEa (a : Fin N) := frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR (some a) H hH
  have hsmooth := PreferredMixedSmoothOn.sum (fun a => (hB a).mul (hEa a))
  have hpar : ‖frameJet τ p m (frameStep τ p m none H) xs s θ‖≤
      A*D^2/d^(h+2+xs.length) := by
    rw [frameJet_step]
    have hh := hHj (xs++[none]) (by simpa using Nat.add_le_add_right hxs 1)
    have hnone : (xs++[none]).length=xs.length+1 := by simp
    rw [hnone] at hh
    apply hh.trans
    have hr := mul_le_mul_of_nonneg_left
      (inverse_power_raise d D hd hdD (h+xs.length+1) 1) hA
    have hDD : D≤D^2 := by nlinarith
    have he : h+xs.length+1+1=h+2+xs.length := by omega
    have hr' : A/d^(h+xs.length+1)≤A*D/d^(h+2+xs.length) := by
      simpa only [←mul_div_assoc,mul_one,pow_one,he] using hr
    exact hr'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDD hA) (by positivity))
  have hcoord (a : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖frameJet τ p m (frameStep τ p m (some a) H) ys s θ‖≤
        A/d^((h+1)+ys.length) := by
    rw [frameJet_step]
    have hh := hHj (ys++[some a]) (by simpa using Nat.add_le_add_right hys 1)
    have hsome : (ys++[some a]).length=ys.length+1 := by
      simp
    rw [hsome] at hh
    convert hh using 1
    congr 2
    omega
  have hterm (a : Fin N) :
      ‖frameJet τ p m (fun t x => B a t x*frameStep τ p m (some a) H t x) xs s θ‖≤
        2^J*B₀*A/d^(h+2+xs.length) := by
    have hh := frameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hpoint hR
      (B a) (frameStep τ p m (some a) H) (hB a) (hEa a) s θ hz
      J 1 (h+1) B₀ A d hB₀ hA hd (hBj a) (hcoord a) xs hxs
    convert hh using 1
    congr 2
    omega
  have htr : ‖frameJet τ p m (fun t x =>
      ∑ a, B a t x*frameStep τ p m (some a) H t x) xs s θ‖≤
      (N:ℝ)*2^J*B₀*A/d^(h+2+xs.length) := by
    rw [frameJet_sum τ δ p m hp hm Ω hΩ hpoint hR _
      (fun a => (hB a).mul (hEa a)) xs s θ hz]
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (fun a _ => hterm a)).trans_eq (by simp; ring)
  have hpot : ‖frameJet τ p m (fun t x => P t x*H t x) xs s θ‖≤
      2^J*P₀*A/d^(h+2+xs.length) := by
    have hh := frameJet_mul_weighted_bound τ δ p m hp hm Ω hΩ hpoint hR P H hP hH s θ hz
      J 2 h P₀ A d hP₀ hA hd hPj (fun ys hys => hHj ys (by omega)) xs hxs
    convert hh using 1
    congr 2
    omega
  have he : vandermondeTransportStep τ p m C H=(fun t x =>
      frameStep τ p m none H t x+
      (∑ a, B a t x*frameStep τ p m (some a) H t x)+P t x*H t x) := by
    funext t x
    exact vandermondeTransportStep_eq τ p m C H t x
  rw [he,frameJet_add τ δ p m hp hm Ω hΩ hpoint hR _ _ (hEs.add hsmooth) (hP.mul hH) xs s θ hz,
    frameJet_add τ δ p m hp hm Ω hΩ hpoint hR _ _ hEs hsmooth xs s θ hz]
  apply (norm_add_le _ _).trans
  have hn := norm_add_le
    (frameJet τ p m (frameStep τ p m none H) xs s θ)
    (frameJet τ p m (fun t x => ∑ a, B a t x*frameStep τ p m (some a) H t x) xs s θ)
  calc
    _ ≤ (‖frameJet τ p m (frameStep τ p m none H) xs s θ‖+
        ‖frameJet τ p m (fun t x => ∑ a, B a t x*frameStep τ p m (some a) H t x) xs s θ‖)+
        ‖frameJet τ p m (fun t x => P t x*H t x) xs s θ‖ :=
      add_le_add hn le_rfl
    _ ≤ (A*D^2/d^(h+2+xs.length)+
        (N:ℝ)*2^J*B₀*A/d^(h+2+xs.length))+
        2^J*P₀*A/d^(h+2+xs.length) :=
      add_le_add (add_le_add hpar htr) hpot
    _ = _ := by ring

/-- Joint induction on transport order and remaining frame words. The
complete loss is exactly twice the transport order plus the coordinate
word count. The hypotheses concern only original seed/B/C factors. -/
theorem vandermondeScalar_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (A₀ B₀ C₀ d D : ℝ) (hA₀ : 0≤A₀) (hB₀ : 0≤B₀) (hC₀ : 0≤C₀)
    (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hAj : ∀ xs, xs.length≤k → ‖frameJet τ p m A xs s θ‖≤A₀)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+xs.length))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => C t x i j) xs s θ‖≤
        C₀/d^(2+xs.length)) :
    ∀ j : ℕ, j≤k → ∀ xs : List (Option (Fin N)), xs.length+j≤k →
    ‖frameJet τ p m (vandermondeScalar τ p m C A j) xs s θ‖≤
      (A₀*D^k)*(D^2+2^k*(2*(N:ℝ)*B₀+2*(N:ℝ)^2*C₀))^j/
        d^(2*j+xs.length) := by
  let P₀ := (N:ℝ)*B₀+2*(N:ℝ)^2*C₀
  let S := D^2+2^k*((N:ℝ)*B₀+P₀)
  have hP₀ : 0≤P₀ := by dsimp [P₀]; positivity
  have hD₀ : 0≤D := le_trans (by norm_num) hD
  have hS : 0≤S := by dsimp [S]; positivity
  have hPm := vandermondePotential_mixed τ δ p m hp hm C Ω hΩ hpoint hR hB hC
  have hPj := vandermondePotential_frame_bound τ δ p m hp hm C Ω hΩ hpoint hR hB hC
    s θ hz k B₀ C₀ d hB₀ hC₀ hd hBj hCj
  have heS : S=D^2+2^k*(2*(N:ℝ)*B₀+2*(N:ℝ)^2*C₀) := by dsimp [S,P₀]; ring
  rw [←heS]
  intro j
  induction j with
  | zero =>
    intro _ xs hxs
    simpa [vandermondeScalar] using frameJet_bounded_to_weighted τ p m A s θ
      k A₀ d D hA₀ hd hdD hD hAj xs (by omega)
  | succ j ih =>
    intro hjk xs hxs
    let remaining := k-(j+1)
    have hmj : remaining≤k := Nat.sub_le _ _
    have hxs' : xs.length≤remaining := by dsimp [remaining]; omega
    have hHj (ys : List (Option (Fin N))) (hys : ys.length≤remaining+1) :
        ‖frameJet τ p m (vandermondeScalar τ p m C A j) ys s θ‖≤
          ((A₀*D^k)*S^j)/d^(2*j+ys.length) := by
      apply ih (by omega) ys
      dsimp [remaining] at hys
      omega
    have hh := vandermondeTransportStep_frame_bound τ δ p m hp hm C
      (vandermondeScalar τ p m C A j) Ω hΩ hpoint hR hB hPm
      (vandermondeScalar_mixed_frames τ δ p m hp hm C A Ω hΩ hpoint hR hB hC hA j)
      s θ hz remaining (2*j) ((A₀*D^k)*S^j) B₀ P₀ d D (by positivity) hB₀ hP₀ hd hdD hD
      (fun a ys hys => hBj a ys (by omega))
      (fun ys hys => hPj ys (hys.trans hmj)) hHj xs hxs'
    have hfactor : D^2+2^remaining*((N:ℝ)*B₀+P₀)≤S := by
      dsimp only [S]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hmj)
        (by positivity : 0≤(N:ℝ)*B₀+P₀))
    change ‖frameJet τ p m
      (vandermondeTransportStep τ p m C (vandermondeScalar τ p m C A j)) xs s θ‖≤_
    calc
      _ ≤ ((A₀*D^k)*S^j)*(D^2+2^remaining*((N:ℝ)*B₀+P₀))/d^(2*j+2+xs.length) := hh
      _ ≤ ((A₀*D^k)*S^j)*S/d^(2*j+2+xs.length) := by
        gcongr
      _ = (A₀*D^k)*S^(j+1)/d^(2*(j+1)+xs.length) := by
        rw [pow_succ]
        congr 1
        ring

end
end IsingBulk.HT22.Tail
