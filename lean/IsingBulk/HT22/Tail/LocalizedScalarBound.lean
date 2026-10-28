import IsingBulk.HT22.Tail.LocalizedTransport

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem frameJet_zero (N : ℕ) (τ : ℝ) (p m : ℝ → ℝ) (xs : List (Option (Fin N))) :
    frameJet τ p m (fun _ _ => 0) xs=fun _ _ => 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [frameJet_cons,ih]
    exact frameStep_zero τ p m a

theorem scalarIterate_eq_zeroSlope {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (j : ℕ) :
    scalarIterate τ p m A j=vandermondeScalar τ p m (fun _ _ _ _ => 0) A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext s θ
    simp only [scalarIterate,vandermondeScalar,vandermondeTransportStep,ih,
      preferredUpperPairSum,Finset.sum_const_zero,mul_zero,zero_mul,add_zero]

/-- Any genuinely smooth source seed, including an arbitrary localized
weight, has the same explicit fixed-order far bound. No descendant is an
input: only the seed and the new residual field's primitive frame jets. -/
theorem scalarIterate_frame_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hB : ∀ a, PreferredMixedSmoothOn
      (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (A₀ B₀ d D : ℝ) (hA₀ : 0≤A₀) (hB₀ : 0≤B₀)
    (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hAj : ∀ xs, xs.length≤k → ‖frameJet τ p m A xs s θ‖≤A₀)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/d^(1+xs.length)) :
    ∀ j : ℕ, j≤k → ∀ xs : List (Option (Fin N)), xs.length+j≤k →
    ‖frameJet τ p m (scalarIterate τ p m A j) xs s θ‖≤
      (A₀*D^k)*(D^2+2^k*(2*(N:ℝ)*B₀))^j/d^(2*j+xs.length) := by
  have hh := vandermondeScalar_frame_bound τ δ p m hp hm (fun _ _ _ _ => 0) A Ω hΩ hpoint hR hB
    (fun _ _ => PreferredMixedSmoothOn.const Ω 0) hA s θ hz k A₀ B₀ 0 d D hA₀ hB₀ le_rfl hd hdD hD
    hAj hBj (fun _ _ xs _ => by rw [frameJet_zero]; simp)
  intro j hj xs hxs
  simpa only [scalarIterate_eq_zeroSlope,mul_zero,add_zero] using hh j hj xs hxs

end
end IsingBulk.HT22.Tail
