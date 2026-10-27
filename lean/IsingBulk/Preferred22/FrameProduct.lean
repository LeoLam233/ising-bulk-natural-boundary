import IsingBulk.Preferred22.CoefficientCalculus
import IsingBulk.Preferred22.CoefficientNorm

/-! Genuine frame Leibniz formulas and fixed-order product bounds. The
product bound is exponential in particle count, with no factorial loss. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredWordSplits {α : Type*} : List α → List (List α × List α)
  | [] => [([],[])]
  | a::xs => (preferredWordSplits xs).flatMap (fun lr =>
      [(a::lr.1,lr.2),(lr.1,a::lr.2)])

theorem preferredWordSplits_length {α : Type*} (xs : List α) :
    (preferredWordSplits xs).length=2^xs.length := by
  induction xs with
  | nil => simp [preferredWordSplits]
  | cons a xs ih =>
    rw [preferredWordSplits,list_flatMap_length_eq _ _ 2 (by intro _ _; rfl),ih]
    simp [pow_succ]

theorem preferredWordSplits_orders {α : Type*} (xs : List α) (lr : List α × List α)
    (hlr : lr∈preferredWordSplits xs) : lr.1.length+lr.2.length=xs.length := by
  induction xs generalizing lr with
  | nil =>
    have he : lr=([],[]) := by simpa [preferredWordSplits] using hlr
    rw [he]
    rfl
  | cons a xs ih =>
    simp only [preferredWordSplits,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hlr
    obtain ⟨uv,huv,h⟩ := hlr
    have hh := ih uv huv
    rcases h with rfl | rfl <;> simp only [List.length_cons] <;> omega

theorem preferredWordSplits_coordinateOrder {N : ℕ} (xs : List (Option (Fin N)))
    (lr : List (Option (Fin N)) × List (Option (Fin N))) (hlr : lr∈preferredWordSplits xs) :
    preferredCoordinateJetOrder lr.1+preferredCoordinateJetOrder lr.2=preferredCoordinateJetOrder xs := by
  induction xs generalizing lr with
  | nil =>
    have he : lr=([],[]) := by simpa [preferredWordSplits] using hlr
    rw [he]
    rfl
  | cons a xs ih =>
    simp only [preferredWordSplits,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hlr
    obtain ⟨uv,huv,h⟩ := hlr
    have hh := ih uv huv
    rcases h with rfl | rfl <;> cases a <;>
      simp [preferredCoordinateJetOrder] at hh ⊢ <;> omega

theorem preferredFrameStep_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameStep τ p m a F s θ=preferredFrameStep τ p m a G s θ := by
  cases a with
  | none => exact preferredParameterFrame_congr_open τ p m F G Ω hΩ he s θ hz
  | some a => exact preferredCoordinateFrame_congr_open τ p m a F G Ω hΩ he s θ hz

theorem preferredFrameJet_mul {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => F t x*G t x) xs s θ=
      ((preferredWordSplits xs).map (fun lr =>
        preferredFrameJet τ p m F lr.1 s θ*preferredFrameJet τ p m G lr.2 s θ)).sum := by
  induction xs generalizing s θ with
  | nil => simp [preferredFrameJet,preferredWordSplits]
  | cons a xs ih =>
    have hFm (ys : List (Option (Fin N))) := preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint F hF ys
    have hGm (ys : List (Option (Fin N))) := preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint G hG ys
    rw [preferredFrameJet_cons]
    rw [preferredFrameStep_congr_open τ p m a _
      (fun t x => ((preferredWordSplits xs).map (fun lr =>
        preferredFrameJet τ p m F lr.1 t x*preferredFrameJet τ p m G lr.2 t x)).sum)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [preferredFrameStep_list_sum τ p m a
      (fun (lr : List (Option (Fin N)) × List (Option (Fin N))) t x =>
        preferredFrameJet τ p m F lr.1 t x*preferredFrameJet τ p m G lr.2 t x)
      (preferredWordSplits xs) Ω (fun lr _ => (hFm lr.1).mul (hGm lr.2)) s θ hz]
    simp only [preferredWordSplits,list_sum_map_flatMap,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    apply congrArg List.sum
    apply List.map_congr_left
    intro lr _
    rw [preferredFrameStep_mul τ p m a _ _ s θ ((hFm lr.1) (s,θ) hz).2 ((hGm lr.2) (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ ((hFm lr.1) (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ ((hGm lr.2) (s,θ) hz).1)]
    simp only [preferredFrameJet_cons]

theorem preferredFrameJet_mul_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F G : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j : ℕ) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hFb : ∀ xs, xs.length≤j → ‖preferredFrameJet τ p m F xs s θ‖≤A)
    (hGb : ∀ xs, xs.length≤j → ‖preferredFrameJet τ p m G xs s θ‖≤B)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖preferredFrameJet τ p m (fun t x => F t x*G t x) xs s θ‖≤2^j*A*B := by
  rw [preferredFrameJet_mul τ δ p m hp hm Ω hΩ hpoint F G hF hG xs s θ hz]
  have hb := norm_list_sum_map_bound (preferredWordSplits xs)
    (fun lr => preferredFrameJet τ p m F lr.1 s θ*preferredFrameJet τ p m G lr.2 s θ) (A*B) (by
      intro lr hlr
      have hh := preferredWordSplits_orders xs lr hlr
      rw [norm_mul]
      exact mul_le_mul (hFb lr.1 (by omega)) (hGb lr.2 (by omega)) (norm_nonneg _) hA)
  rw [preferredWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hb
  exact hb.trans (by
    have hh : (2:ℝ)^xs.length≤2^j := pow_le_pow_right₀ (by norm_num) hxs
    nlinarith [mul_nonneg hA hB])

theorem preferredFrameStep_const {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N)) (c : ℂ) :
    preferredFrameStep τ p m a (fun _ _ => c)=(fun _ _ => 0) := by
  funext s θ
  cases a <;> simp [preferredFrameStep,preferredParameterFrame,preferredCoordinateFrame]

theorem preferredFrameJet_const {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (c : ℂ)
    (xs : List (Option (Fin N))) :
    preferredFrameJet τ p m (fun _ _ => c) xs=(fun _ _ => if xs=[] then c else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [preferredFrameJet_cons,ih,preferredFrameStep_const]
    rfl

theorem preferredFrameJet_list_prod_bound {N : ℕ} {ι : Type*}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (j : ℕ) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ i∈L, ∀ xs, xs.length≤j → ‖preferredFrameJet τ p m (F i) xs s θ‖≤C)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖preferredFrameJet τ p m (fun t x => (L.map (fun i => F i t x)).prod) xs s θ‖≤(2^j*C)^L.length := by
  induction L generalizing xs with
  | nil => simp [preferredFrameJet_const]; split_ifs <;> norm_num
  | cons i L ih =>
    have ht := PreferredMixedSmoothOn.list_prod (fun i z => F i z.1 z.2) L Ω
      (fun k hk => hF k (List.mem_cons_of_mem _ hk))
    have hi := hF i (List.mem_cons_self ..)
    have hh := preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint (F i)
      (fun t x => (L.map (fun i => F i t x)).prod) hi ht s θ hz j C ((2^j*C)^L.length) hC (by positivity)
      (hbound i (List.mem_cons_self ..))
      (fun ys hys => ih (fun k hk => hF k (List.mem_cons_of_mem _ hk))
        (fun k hk => hbound k (List.mem_cons_of_mem _ hk)) ys hys) xs hxs
    simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using hh

end
end IsingBulk.Preferred22
