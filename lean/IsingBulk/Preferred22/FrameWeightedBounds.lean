import IsingBulk.Preferred22.SeedFrameBound

/-! Exact source-frame linearity and the coordinate-order-weighted
Leibniz bound used for the actual angular representative. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem inverse_power_raise (d D : ℝ) (hd : 0<d) (hdD : d≤D) (a e : ℕ) :
    1/d^a≤D^e/d^(a+e) := by
  calc
    1/d^a = d^e/d^(a+e) := by rw [pow_add]; field_simp [hd.ne']
    _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ hd.le hdD e) (by positivity)

theorem preferredFrameJet_append {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (xs ys : List (Option (Fin N))) :
    preferredFrameJet τ p m (preferredFrameJet τ p m F ys) xs=
      preferredFrameJet τ p m F (xs++ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [preferredFrameJet_cons,ih,List.cons_append,preferredFrameJet_cons]

theorem preferredCoordinateJetOrder_append {N : ℕ} (xs ys : List (Option (Fin N))) :
    preferredCoordinateJetOrder (xs++ys)=preferredCoordinateJetOrder xs+preferredCoordinateJetOrder ys := by
  simp only [preferredCoordinateJetOrder,List.countP_append]

theorem preferredCoordinateJetOrder_le_length {N : ℕ} (xs : List (Option (Fin N))) :
    preferredCoordinateJetOrder xs≤xs.length := List.countP_le_length

/-- Bounded jets can be put in the common coordinate-weighted seminorm
on a source domain of bounded diameter. -/
theorem preferredFrameJet_bounded_to_weighted {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (j : ℕ) (A d D : ℝ) (hA : 0≤A) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (hF : ∀ xs, xs.length≤j → ‖preferredFrameJet τ p m F xs s θ‖≤A)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖preferredFrameJet τ p m F xs s θ‖≤A*D^j/d^(preferredCoordinateJetOrder xs) := by
  have hh := inverse_power_loss_bound d D hd hdD hD 0 (preferredCoordinateJetOrder xs) j
    (Nat.zero_le _) ((preferredCoordinateJetOrder_le_length xs).trans hxs)
  simp only [pow_zero,div_one] at hh
  apply (hF xs hxs).trans
  have hm := mul_le_mul_of_nonneg_left hh hA
  simpa only [mul_one,mul_div_assoc] using hm

theorem preferredFrameJet_list_sum {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => (L.map (fun i => F i t x)).sum) xs s θ=
      (L.map (fun i => preferredFrameJet τ p m (F i) xs s θ)).sum := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    rw [preferredFrameJet_cons]
    rw [preferredFrameStep_congr_open τ p m a _
      (fun t x => (L.map (fun i => preferredFrameJet τ p m (F i) xs t x)).sum)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [preferredFrameStep_list_sum τ p m a
      (fun i t x => preferredFrameJet τ p m (F i) xs t x) L Ω
      (fun i hi => preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint (F i) (hF i hi) xs)
      s θ hz]
    simp only [preferredFrameJet_cons]

theorem preferredFrameJet_finset_sum {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (S : Finset ι)
    (hF : ∀ i∈S, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => ∑ i∈S, F i t x) xs s θ=
      ∑ i∈S, preferredFrameJet τ p m (F i) xs s θ := by
  simpa only [Finset.sum_map_toList] using preferredFrameJet_list_sum τ δ p m hp hm
    Ω hΩ hpoint F S.toList (fun i hi => hF i (Finset.mem_toList.mp hi)) xs s θ hz

theorem preferredFrameJet_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ)
    (hF : ∀ i, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => ∑ i, F i t x) xs s θ=
      ∑ i, preferredFrameJet τ p m (F i) xs s θ := by
  simpa only [Finset.sum_map_toList] using preferredFrameJet_list_sum τ δ p m hp hm
    Ω hΩ hpoint F Finset.univ.toList (fun i _ => hF i) xs s θ hz

theorem preferredFrameJet_add {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => F t x+G t x) xs s θ=
      preferredFrameJet τ p m F xs s θ+preferredFrameJet τ p m G xs s θ := by
  have hmix (H : ℂ → (Fin N → ℝ) → ℂ) (hH : H∈[F,G]) :
      PreferredMixedSmoothOn (fun z => H z.1 z.2) Ω := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hH
    rcases hH with rfl | rfl
    · exact hF
    · exact hG
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
    preferredFrameJet_list_sum τ δ p m hp hm Ω hΩ hpoint (fun H => H) [F,G] hmix xs s θ hz

theorem preferredFrameJet_sub {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => F t x-G t x) xs s θ=
      preferredFrameJet τ p m F xs s θ-preferredFrameJet τ p m G xs s θ := by
  have hfun : (fun t x => F t x-G t x)=(fun t x => F t x+(-1:ℂ)*G t x) := by
    funext t x
    ring
  rw [hfun,preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint F (fun t x => (-1:ℂ)*G t x)
    hF ((PreferredMixedSmoothOn.const Ω (-1)).mul hG) xs s θ hz,
    preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hpoint G hG (-1) xs s θ hz]
  ring

/-- Coordinate-order losses add exactly under the genuine frame Leibniz
formula. Parameter-frame derivatives incur no hidden diameter loss. -/
theorem preferredFrameJet_mul_weighted_bound {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j a b : ℕ)
    (A B d : ℝ) (hA : 0≤A) (hB : 0≤B) (hd : 0<d)
    (hFb : ∀ xs, xs.length≤j →
      ‖preferredFrameJet τ p m F xs s θ‖≤A/d^(a+preferredCoordinateJetOrder xs))
    (hGb : ∀ xs, xs.length≤j →
      ‖preferredFrameJet τ p m G xs s θ‖≤B/d^(b+preferredCoordinateJetOrder xs))
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖preferredFrameJet τ p m (fun t x => F t x*G t x) xs s θ‖≤
      2^j*A*B/d^(a+b+preferredCoordinateJetOrder xs) := by
  rw [preferredFrameJet_mul τ δ p m hp hm Ω hΩ hpoint F G hF hG xs s θ hz]
  have hb := norm_list_sum_map_bound (preferredWordSplits xs)
    (fun lr => preferredFrameJet τ p m F lr.1 s θ*preferredFrameJet τ p m G lr.2 s θ)
    (A*B/d^(a+b+preferredCoordinateJetOrder xs)) (by
      intro lr hlr
      have hl := preferredWordSplits_orders xs lr hlr
      have ho := preferredWordSplits_coordinateOrder xs lr hlr
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
    (show 0≤A*B/d^(a+b+preferredCoordinateJetOrder xs) by positivity)
  convert hm using 1
  ring

end
end IsingBulk.Preferred22
