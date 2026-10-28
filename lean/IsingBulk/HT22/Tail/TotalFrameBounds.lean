import IsingBulk.HT22.Tail.FrameProducts
import IsingBulk.Preferred22.FrameWeightedBounds

/-! Total-order weighted Leibniz bounds for the fixed-v source frames.
Parameter and coordinate jets both pay the manuscript scale power. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem frameJet_append {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (xs ys : List (Option (Fin N))) :
    frameJet τ p m (frameJet τ p m F ys) xs=
      frameJet τ p m F (xs++ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [frameJet_cons,ih,List.cons_append,frameJet_cons]

/-- Bounded jets can be put in the common coordinate-weighted seminorm
on a source domain of bounded diameter. -/
theorem frameJet_bounded_to_weighted {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (j : ℕ) (A d D : ℝ) (hA : 0≤A) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hF : ∀ xs, xs.length≤j → ‖frameJet τ p m F xs s θ‖≤A)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m F xs s θ‖≤A*D^j/d^(xs.length) := by
  have hh := inverse_power_loss_bound d D hd hdD hD 0 (xs.length) j
    (Nat.zero_le _) hxs
  simp only [pow_zero,div_one] at hh
  apply (hF xs hxs).trans
  have hm := mul_le_mul_of_nonneg_left hh hA
  simpa only [mul_one,mul_div_assoc] using hm

theorem frameJet_list_sum {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => (L.map (fun i => F i t x)).sum) xs s θ=
      (L.map (fun i => frameJet τ p m (F i) xs s θ)).sum := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    rw [frameJet_cons]
    rw [frameStep_congr_open τ p m a _
      (fun t x => (L.map (fun i => frameJet τ p m (F i) xs t x)).sum)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [frameStep_list_sum τ p m a
      (fun i t x => frameJet τ p m (F i) xs t x) L Ω
      (fun i hi => frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR (F i) (hF i hi) xs)
      s θ hz]
    simp only [frameJet_cons]

theorem frameJet_finset_sum {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (S : Finset ι)
    (hF : ∀ i∈S, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => ∑ i∈S, F i t x) xs s θ=
      ∑ i∈S, frameJet τ p m (F i) xs s θ := by
  simpa only [Finset.sum_map_toList] using frameJet_list_sum τ δ p m hp hm
    Ω hΩ hpoint hR F S.toList (fun i hi => hF i (Finset.mem_toList.mp hi)) xs s θ hz

theorem frameJet_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ)
    (hF : ∀ i, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => ∑ i, F i t x) xs s θ=
      ∑ i, frameJet τ p m (F i) xs s θ := by
  simpa only [Finset.sum_map_toList] using frameJet_list_sum τ δ p m hp hm
    Ω hΩ hpoint hR F Finset.univ.toList (fun i _ => hF i) xs s θ hz

theorem frameJet_add {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => F t x+G t x) xs s θ=
      frameJet τ p m F xs s θ+frameJet τ p m G xs s θ := by
  have hmix (H : ℂ → (Fin N → ℝ) → ℂ) (hH : H∈[F,G]) :
      PreferredMixedSmoothOn (fun z => H z.1 z.2) Ω := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hH
    rcases hH with rfl | rfl
    · exact hF
    · exact hG
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
    frameJet_list_sum τ δ p m hp hm Ω hΩ hpoint hR (fun H => H) [F,G] hmix xs s θ hz

theorem frameJet_sub {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => F t x-G t x) xs s θ=
      frameJet τ p m F xs s θ-frameJet τ p m G xs s θ := by
  have hfun : (fun t x => F t x-G t x)=(fun t x => F t x+(-1:ℂ)*G t x) := by
    funext t x
    ring
  rw [hfun,frameJet_add τ δ p m hp hm Ω hΩ hpoint hR F (fun t x => (-1:ℂ)*G t x)
    hF ((PreferredMixedSmoothOn.const Ω (-1)).mul hG) xs s θ hz,
    frameJet_const_mul τ δ p m hp hm Ω hΩ hpoint hR G hG (-1) xs s θ hz]
  ring

/-- Coordinate-order losses add exactly under the genuine frame Leibniz
formula. Parameter-frame derivatives cost one scale power, like coordinate derivatives. -/
theorem frameJet_mul_weighted_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j a b : ℕ)
    (A B d : ℝ) (hA : 0≤A) (hB : 0≤B) (hd : 0<d)
    (hFb : ∀ xs, xs.length≤j →
      ‖frameJet τ p m F xs s θ‖≤A/d^(a+xs.length))
    (hGb : ∀ xs, xs.length≤j →
      ‖frameJet τ p m G xs s θ‖≤B/d^(b+xs.length))
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m (fun t x => F t x*G t x) xs s θ‖≤
      2^j*A*B/d^(a+b+xs.length) := by
  rw [frameJet_mul τ δ p m hp hm Ω hΩ hpoint hR F G hF hG xs s θ hz]
  have hb := norm_list_sum_map_bound (preferredWordSplits xs)
    (fun lr => frameJet τ p m F lr.1 s θ*frameJet τ p m G lr.2 s θ)
    (A*B/d^(a+b+xs.length)) (by
      intro lr hlr
      have hl := preferredWordSplits_orders xs lr hlr
      rw [norm_mul]
      apply (mul_le_mul (hFb lr.1 (by omega)) (hGb lr.2 (by omega))
        (norm_nonneg _) (by positivity)).trans_eq
      rw [div_mul_div_comm,←pow_add]
      congr 2
      omega)
  rw [preferredWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hb
  apply hb.trans
  have hh : (2:ℝ)^xs.length≤2^j := pow_le_pow_right₀ (by norm_num) hxs
  have hm := mul_le_mul_of_nonneg_right hh
    (show 0≤A*B/d^(a+b+xs.length) by positivity)
  convert hm using 1
  ring

end
end IsingBulk.HT22.Tail
