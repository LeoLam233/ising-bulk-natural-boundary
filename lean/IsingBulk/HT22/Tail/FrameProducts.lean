import IsingBulk.HT22.Tail.FrameCalculus
import IsingBulk.Preferred22.FrameProduct

/-! Actual fixed-v frame Leibniz rules. Only the field-independent word
splits and count are reused. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem frameStep_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (heq : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameStep τ p m a F s θ=frameStep τ p m a G s θ := by
  have he : (fun z : ℂ × (Fin N → ℝ) => F z.1 z.2) =ᶠ[𝓝 (s,θ)] (fun z => G z.1 z.2) := by
    filter_upwards [hΩ.mem_nhds hz] with z hz'
    exact heq z hz'
  have hs : deriv (fun t : ℂ => F t θ) s=deriv (fun t : ℂ => G t θ) s := by
    exact (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s)).deriv_eq
  have hx (i : Fin N) : deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)=
      deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i) := by
    have hc : Continuous (fun x : ℝ => (s,Function.update θ i x)) := by fun_prop
    have ht : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      simpa only [Function.update_eq_self] using hc.tendsto (θ i)
    exact (he.comp_tendsto ht).deriv_eq
  cases a <;> simp only [frameStep,parameterFrame,coordinateFrame,hs,hx]

theorem frameJet_mul {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => F t x*G t x) xs s θ=
      ((preferredWordSplits xs).map (fun lr =>
        frameJet τ p m F lr.1 s θ*frameJet τ p m G lr.2 s θ)).sum := by
  induction xs generalizing s θ with
  | nil => simp [frameJet,preferredWordSplits]
  | cons a xs ih =>
    have hFm (ys : List (Option (Fin N))) := frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR F hF ys
    have hGm (ys : List (Option (Fin N))) := frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR G hG ys
    rw [frameJet_cons]
    rw [frameStep_congr_open τ p m a _
      (fun t x => ((preferredWordSplits xs).map (fun lr =>
        frameJet τ p m F lr.1 t x*frameJet τ p m G lr.2 t x)).sum)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [frameStep_list_sum τ p m a
      (fun (lr : List (Option (Fin N)) × List (Option (Fin N))) t x =>
        frameJet τ p m F lr.1 t x*frameJet τ p m G lr.2 t x)
      (preferredWordSplits xs) Ω (fun lr _ => (hFm lr.1).mul (hGm lr.2)) s θ hz]
    simp only [preferredWordSplits,list_sum_map_flatMap,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    apply congrArg List.sum
    apply List.map_congr_left
    intro lr _
    rw [frameStep_mul τ p m a _ _ s θ ((hFm lr.1) (s,θ) hz).2 ((hGm lr.2) (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ ((hFm lr.1) (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ ((hGm lr.2) (s,θ) hz).1)]
    simp only [frameJet_cons]

theorem frameJet_mul_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j : ℕ) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hFb : ∀ xs, xs.length≤j → ‖frameJet τ p m F xs s θ‖≤A)
    (hGb : ∀ xs, xs.length≤j → ‖frameJet τ p m G xs s θ‖≤B)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m (fun t x => F t x*G t x) xs s θ‖≤2^j*A*B := by
  rw [frameJet_mul τ δ p m hp hm Ω hΩ hpoint hR F G hF hG xs s θ hz]
  have hb := norm_list_sum_map_bound (preferredWordSplits xs)
    (fun lr => frameJet τ p m F lr.1 s θ*frameJet τ p m G lr.2 s θ) (A*B) (by
      intro lr hlr
      have hh := preferredWordSplits_orders xs lr hlr
      rw [norm_mul]
      exact mul_le_mul (hFb lr.1 (by omega)) (hGb lr.2 (by omega)) (norm_nonneg _) hA)
  rw [preferredWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hb
  exact hb.trans (by
    have hh : (2:ℝ)^xs.length≤2^j := pow_le_pow_right₀ (by norm_num) hxs
    nlinarith [mul_nonneg hA hB])

theorem frameStep_const {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N)) (c : ℂ) :
    frameStep τ p m a (fun _ _ => c)=(fun _ _ => 0) := by
  funext s θ
  cases a <;> simp [frameStep,parameterFrame,coordinateFrame]

theorem frameJet_const {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (c : ℂ)
    (xs : List (Option (Fin N))) :
    frameJet τ p m (fun _ _ => c) xs=(fun _ _ => if xs=[] then c else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [frameJet_cons,ih,frameStep_const]
    rfl

theorem frameJet_list_prod_bound {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j : ℕ) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ i∈L, ∀ xs, xs.length≤j → ‖frameJet τ p m (F i) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖frameJet τ p m (fun t x => (L.map (fun i => F i t x)).prod) xs s θ‖≤(2^j*C)^L.length := by
  induction L generalizing xs with
  | nil => simp [frameJet_const]; split_ifs <;> norm_num
  | cons i L ih =>
    have ht := PreferredMixedSmoothOn.list_prod (fun i z => F i z.1 z.2) L Ω
      (fun k hk => hF k (List.mem_cons_of_mem _ hk))
    have hi := hF i (List.mem_cons_self ..)
    have hh := frameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint hR (F i)
      (fun t x => (L.map (fun i => F i t x)).prod) hi ht s θ hz j C ((2^j*C)^L.length) hC (by positivity)
      (hbound i (List.mem_cons_self ..))
      (fun ys hys => ih (fun k hk => hF k (List.mem_cons_of_mem _ hk))
        (fun k hk => hbound k (List.mem_cons_of_mem _ hk)) ys hys) xs hxs
    simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using hh

theorem frameJet_const_mul {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (c : ℂ) (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameJet τ p m (fun t x => c*F t x) xs s θ=
      c*frameJet τ p m F xs s θ := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    have hmixed := frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR F hF xs
    rw [frameJet_cons]
    rw [frameStep_congr_open τ p m a _
      (fun t x => c*frameJet τ p m F xs t x) Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [frameStep_mul τ p m a (fun _ _ => c) _ s θ
      (differentiableAt_const c) (hmixed (s,θ) hz).2
      (fun _ => differentiableAt_const c)
      (preferredMixed_coordinate_differentiable _ s θ (hmixed (s,θ) hz).1)]
    rw [frameStep_const]
    simp only [zero_mul,zero_add,frameJet_cons]


end
end IsingBulk.HT22.Tail
