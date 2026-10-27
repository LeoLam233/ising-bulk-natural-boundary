import IsingBulk.Preferred22.FramePullback
import IsingBulk.Preferred22.CollectiveCauchyJets

/-! All genuine source-frame words are identified with canonical complex
partial words on analytic pullbacks. This is an exact calculus statement,
and preserves the count of coordinate derivatives. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredComplexFrameDirection {N : ℕ} : Option (Fin N) → ℂ × (Fin N → ℂ)
  | none => (1,0)
  | some a => (0,Pi.single a 1)

def preferredFrameDirections {N : ℕ} :
    (xs : List (Option (Fin N))) → Fin xs.length → ℂ × (Fin N → ℂ)
  | [] => Fin.elim0
  | a::xs => Fin.cons (preferredComplexFrameDirection a) (preferredFrameDirections xs)

def preferredComplexFrameJet {N : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ × (Fin N → ℂ) → F) : List (Option (Fin N)) → ℂ × (Fin N → ℂ) → F
  | [] => f
  | a::xs => fun z => fderiv ℂ (preferredComplexFrameJet f xs) z (preferredComplexFrameDirection a)

theorem preferredComplexFrameJet_analyticAt {N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ × (Fin N → ℂ) → F) (xs : List (Option (Fin N)))
    (z : ℂ × (Fin N → ℂ)) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (preferredComplexFrameJet f xs) z := by
  induction xs with
  | nil => exact hf
  | cons a xs ih =>
    exact ((ContinuousLinearMap.apply ℂ F (preferredComplexFrameDirection a)).analyticAt _).comp ih.fderiv

theorem preferredComplexFrameJet_eq_iteratedFDeriv {N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ × (Fin N → ℂ) → F) (xs : List (Option (Fin N)))
    (z : ℂ × (Fin N → ℂ)) (hf : AnalyticAt ℂ f z) :
    preferredComplexFrameJet f xs z=
      iteratedFDeriv ℂ xs.length f z (preferredFrameDirections xs) := by
  induction xs generalizing z with
  | nil => simp only [preferredComplexFrameJet,List.length_nil,iteratedFDeriv_zero_apply]
  | cons a xs ih =>
    have he : preferredComplexFrameJet f xs =ᶠ[𝓝 z]
        (fun x => iteratedFDeriv ℂ xs.length f x (preferredFrameDirections xs)) := by
      filter_upwards [hf.eventually_analyticAt] with x hx
      exact ih x hx
    change fderiv ℂ (preferredComplexFrameJet f xs) z (preferredComplexFrameDirection a)=_
    rw [he.fderiv_eq]
    have hlt : (xs.length:ℕ∞ω)<∞ := by exact_mod_cast ENat.natCast_lt_top xs.length
    have hdiff := (hf.contDiffAt (n:=∞)).differentiableAt_iteratedFDeriv hlt
    rw [fderiv_continuousMultilinear_apply_const_apply hdiff]
    rfl

theorem preferredComplexFrameJet_apply {N : ℕ}
    (f : ℂ × (Fin N → ℂ) → (Fin N → ℂ)) (xs : List (Option (Fin N)))
    (z : ℂ × (Fin N → ℂ)) (hf : AnalyticAt ℂ f z) (i : Fin N) :
    preferredComplexFrameJet (fun x => f x i) xs z=preferredComplexFrameJet f xs z i := by
  induction xs generalizing z with
  | nil => rfl
  | cons a xs ih =>
    have he : preferredComplexFrameJet (fun x => f x i) xs =ᶠ[𝓝 z]
        (fun x => preferredComplexFrameJet f xs x i) := by
      filter_upwards [hf.eventually_analyticAt] with x hx
      exact ih x hx
    change fderiv ℂ (preferredComplexFrameJet (fun x => f x i) xs) z
      (preferredComplexFrameDirection a)=_
    rw [he.fderiv_eq]
    rw [fderiv_apply (preferredComplexFrameJet_analyticAt f xs z hf).differentiableAt i]
    rfl

/-- The anisotropic weight counts only actual q directions. -/
theorem preferredFrameDirections_weight_product {N : ℕ}
    (xs : List (Option (Fin N))) (d : ℝ) (hd : 0<d) :
    (∏ k, max ‖(preferredFrameDirections xs k).1‖
      (‖(preferredFrameDirections xs k).2‖/d)) = 1/d^(preferredCoordinateJetOrder xs) := by
  induction xs with
  | nil => simp [preferredCoordinateJetOrder]
  | cons a xs ih =>
    simp only [List.length_cons,preferredFrameDirections,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [ih]
    cases a with
    | none =>
      simp [preferredComplexFrameDirection,preferredCoordinateJetOrder]
    | some a =>
      simp only [preferredComplexFrameDirection,norm_zero,Pi.norm_single,norm_one,
        max_eq_right (one_div_nonneg.mpr hd.le),
        preferredCoordinateJetOrder,List.countP_cons,Option.isSome_some,ite_true]
      rw [pow_succ]
      ring

theorem preferredFrame_derivatives_congr_open {N : ℕ}
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    deriv (fun t : ℂ => F t θ) s=deriv (fun t : ℂ => G t θ) s ∧
      ∀ i, deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)=
        deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i) := by
  have hh : (fun z : ℂ × (Fin N → ℝ) => F z.1 z.2) =ᶠ[𝓝 (s,θ)] (fun z => G z.1 z.2) := by
    filter_upwards [hΩ.mem_nhds hz] with z hz
    exact he z hz
  constructor
  · exact (hh.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s)).deriv_eq
  · intro i
    have ht : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      simpa only [Function.update_eq_self] using
        ((show Continuous (fun x : ℝ => (s,Function.update θ i x)) by fun_prop).tendsto (θ i))
    exact (hh.comp_tendsto ht).deriv_eq

theorem preferredCoordinateFrame_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Fin N)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredCoordinateFrame τ p m a F s θ=preferredCoordinateFrame τ p m a G s θ := by
  have hh := (preferredFrame_derivatives_congr_open F G Ω hΩ he s θ hz).2
  unfold preferredCoordinateFrame
  simp_rw [hh]

theorem preferredParameterFrame_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredParameterFrame τ p m F s θ=preferredParameterFrame τ p m G s θ := by
  obtain ⟨hs,hθ⟩ := preferredFrame_derivatives_congr_open F G Ω hΩ he s θ hz
  unfold preferredParameterFrame
  rw [hs]
  simp_rw [hθ]

/-- All actual frame words agree with canonical complex partial words on
every open physical chart. There is no assumed commutation identity. -/
theorem preferredFrameJet_pullback_open {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)) xs s θ=
      preferredComplexFrameJet F xs (s,preferredSourceCoordinate τ p m s θ) := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    have he (z : ℂ × (Fin N → ℝ)) (hz : z∈Ω) :
        preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)) xs z.1 z.2=
          preferredComplexFrameJet F xs (z.1,preferredSourceCoordinate τ p m z.1 z.2) := ih z.1 z.2 hz
    have hpart := (preferredComplexFrameJet_analyticAt F xs _ (hF (s,θ) hz)).differentiableAt
    cases a with
    | none =>
      change preferredParameterFrame τ p m
        (preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)) xs) s θ=_
      rw [preferredParameterFrame_congr_open τ p m _
        (fun t x => preferredComplexFrameJet F xs (t,preferredSourceCoordinate τ p m t x)) Ω hΩ he s θ hz]
      exact preferredParameterFrame_pullback τ δ p m hp hm s θ (hpoint (s,θ) hz)
        (preferredComplexFrameJet F xs) hpart
    | some a =>
      change preferredCoordinateFrame τ p m a
        (preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)) xs) s θ=_
      rw [preferredCoordinateFrame_congr_open τ p m a _
        (fun t x => preferredComplexFrameJet F xs (t,preferredSourceCoordinate τ p m t x)) Ω hΩ he s θ hz]
      exact preferredCoordinateFrame_pullback τ δ p m hp hm s θ (hpoint (s,θ) hz)
        (preferredComplexFrameJet F xs) hpart a

end
end IsingBulk.Preferred22
