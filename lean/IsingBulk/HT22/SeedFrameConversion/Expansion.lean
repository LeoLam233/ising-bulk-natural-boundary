import IsingBulk.HT22.SeedFrameConversion.Frames
import IsingBulk.HT22.Tail.FrameProducts
import IsingBulk.Preferred22.CoefficientCalculus

/-! Finite, explicit differential-polynomial frame conversion. The coefficient
alphabet is independent of particle number. -/
namespace IsingBulk.HT22.SeedFrameConversion
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def coefficient : List Bool → ℂ → ℂ
  | [] => fun _ => 1
  | false::cs => deriv (coefficient cs)
  | true::cs => fun t => -deriv preferredMovingBranch t * coefficient cs t

theorem coefficient_analyticAt (cs : List Bool) (t : ℂ) (ht : AnalyticAt ℂ preferredMovingBranch t) :
    AnalyticAt ℂ (coefficient cs) t := by
  induction cs with
  | nil => exact analyticAt_const
  | cons b cs ih =>
    cases b with
    | false => exact ih.deriv
    | true => exact ht.deriv.neg.mul ih

theorem coefficient_mixed {N : ℕ} (cs : List Bool) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : ∀ z∈Ω, AnalyticAt ℂ preferredMovingBranch z.1) :
    PreferredMixedSmoothOn (fun z => coefficient cs z.1) Ω := by
  intro z hz
  have h := coefficient_analyticAt cs z.1 (hΩ z hz)
  exact ⟨h.contDiffAt.restrict_scalars ℝ |>.comp z contDiffAt_fst,h.differentiableAt⟩

abbrev Term (N : ℕ) := List Bool × List (Option (Fin N))

def stepTerms {N : ℕ} (a : Option (Fin N)) (u : Term N) : List (Term N) :=
  match a with
  | some i => [(u.1,some i::u.2)]
  | none => [(false::u.1,u.2),(u.1,none::u.2)] ++
      (List.finRange N).map (fun i => (true::u.1,some i::u.2))

def expansion {N : ℕ} : List (Option (Fin N)) → List (Term N)
  | [] => [([],[])]
  | a::xs => (expansion xs).flatMap (stepTerms a)

def termValue {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (u : Term N) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  coefficient u.1 t * preferredFrameJet τ p m F u.2 t θ

theorem termValue_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω) (u : Term N) :
    PreferredMixedSmoothOn (fun z => termValue τ p m F u z.1 z.2) Ω :=
  (coefficient_mixed u.1 Ω (fun z hz => preferredMovingBranch_analyticAt_upper z.1 (hpoint z hz).trace_im)).mul
    (preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint F hF u.2)

theorem frameStep_coefficient {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (a : Option (Fin N)) (cs : List Bool) (t : ℂ) (θ : Fin N → ℝ) :
    frameStep τ p m a (fun s _ => coefficient cs s) t θ =
      match a with | none => coefficient (false::cs) t | some _ => 0 := by
  cases a <;> simp [frameStep,parameterFrame,coordinateFrame,coefficient]

theorem frameStep_term {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (a : Option (Fin N)) (u : Term N) (t : ℂ) (θ : Fin N → ℝ) (hz : (t,θ)∈Ω) :
    frameStep τ p m a (termValue τ p m F u) t θ =
      ((stepTerms a u).map (fun v => termValue τ p m F v t θ)).sum := by
  have hc := coefficient_mixed u.1 Ω (fun z hz => preferredMovingBranch_analyticAt_upper z.1 (hpoint z hz).trace_im)
  have hj := preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint F hF u.2
  unfold termValue
  rw [frameStep_mul τ p m a _ _ t θ (hc (t,θ) hz).2 (hj (t,θ) hz).2
    (preferredMixed_coordinate_differentiable _ t θ (hc (t,θ) hz).1)
    (preferredMixed_coordinate_differentiable _ t θ (hj (t,θ) hz).1),
    frameStep_coefficient]
  cases a with
  | some i =>
    simp only [stepTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      zero_mul,zero_add,add_zero,frameStep,coordinateFrame_eq_shared,preferredFrameJet]
  | none =>
    simp only [frameStep,parameterFrame_eq_shared τ δ p m _ t θ (hpoint (t,θ) hz),
      stepTerms,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,List.map_map,add_zero,preferredFrameJet,coefficient]
    simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply, coefficient, preferredFrameJet]
    simp only [← Finset.mul_sum]
    ring


theorem frameJet_expansion {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (xs : List (Option (Fin N))) (t : ℂ) (θ : Fin N → ℝ) (hz : (t,θ)∈Ω) :
    frameJet τ p m F xs t θ =
      ((expansion xs).map (fun u => termValue τ p m F u t θ)).sum := by
  induction xs generalizing t θ with
  | nil => simp [frameJet,expansion,termValue,coefficient,preferredFrameJet]
  | cons a xs ih =>
    rw [frameJet_cons]
    rw [frameStep_congr_open τ p m a _
      (fun s x => ((expansion xs).map (fun u => termValue τ p m F u s x)).sum)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) t θ hz]
    rw [frameStep_list_sum τ p m a (termValue τ p m F) (expansion xs) Ω
      (fun u _ => termValue_mixed τ δ p m hp hm Ω hΩ hpoint F hF u) t θ hz]
    simp only [expansion,list_sum_map_flatMap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro u _
    exact frameStep_term τ δ p m hp hm Ω hΩ hpoint F hF a u t θ hz

theorem stepTerms_length_le {N : ℕ} (a : Option (Fin N)) (u : Term N) :
    (stepTerms a u).length ≤ N+2 := by
  cases a <;> simp [stepTerms]

theorem stepTerms_orders {N : ℕ} (a : Option (Fin N)) (u v : Term N)
    (hv : v ∈ stepTerms a u) : v.1.length ≤ u.1.length+1 ∧ v.2.length ≤ u.2.length+1 := by
  cases a with
  | some i =>
    simp only [stepTerms,List.mem_singleton] at hv
    subst v
    simp
  | none =>
    simp only [stepTerms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hv
    rcases hv with (rfl | rfl) | ⟨i,_,rfl⟩ <;> simp

theorem expansion_orders {N : ℕ} (xs : List (Option (Fin N))) (u : Term N)
    (hu : u ∈ expansion xs) : u.1.length ≤ xs.length ∧ u.2.length ≤ xs.length := by
  induction xs generalizing u with
  | nil =>
    simp only [expansion,List.mem_singleton] at hu
    subst u
    simp
  | cons a xs ih =>
    obtain ⟨v,hv,hu⟩ := List.mem_flatMap.mp hu
    obtain ⟨hc,hw⟩ := ih v hv
    obtain ⟨hc',hw'⟩ := stepTerms_orders a v u hu
    simp only [List.length_cons]
    constructor <;> omega

end
end IsingBulk.HT22.SeedFrameConversion
