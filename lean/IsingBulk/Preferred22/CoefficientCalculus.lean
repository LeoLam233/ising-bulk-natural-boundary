import IsingBulk.Preferred22.CoefficientTermCount
import IsingBulk.Preferred22.FrameAlgebra

/-! The differential-polynomial terms evaluate to the actual scalar word
coefficients. The proof uses the genuine frame derivations and actual
kernel material derivative, retaining every real cutoff derivative. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredAtomValue_shift {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    preferredFrameStep τ p m a (preferredAtomValue τ η p m r x)=
      preferredAtomValue τ η p m r (preferredAtomShift a x) := by
  cases x <;> cases a <;> rfl

theorem preferredAtomValue_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ z∈Ω, AnalyticAt ℂ
      (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (a : PreferredCoefficientAtom N) :
    PreferredMixedSmoothOn (fun z => preferredAtomValue τ η p m r a z.1 z.2) Ω := by
  cases a with
  | seed xs =>
    exact preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint _
      (preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint) xs
  | collective i xs =>
    apply preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint _ _ xs
    exact preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun x => preferredResidualCollective x.1 x.2 i)
      (fun z hz => analyticAt_pi_iff.mp (hB z hz) i)
  | kernel ij xs =>
    exact preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint _
      ((preferred_regular_factors_mixed τ δ p m hp hm Ω hpoint).1 ij) xs

theorem preferredTermValue_mixed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => preferredAtomValue τ η p m r a z.1 z.2) Ω)
    (T : PreferredCoefficientTerm N) :
    PreferredMixedSmoothOn (fun z => preferredTermValue τ η p m r T z.1 z.2) Ω :=
  PreferredMixedSmoothOn.list_prod _ T Ω (fun a _ => hA a)

theorem list_sum_map_flatMap {α β : Type*} (L : List α) (F : α → List β) (G : β → ℂ) :
    ((L.flatMap F).map G).sum=(L.map (fun a => ((F a).map G).sum)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem preferredTermDerivative_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => preferredAtomValue τ η p m r a z.1 z.2) Ω)
    (a : Option (Fin N)) (T : PreferredCoefficientTerm N)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameStep τ p m a (preferredTermValue τ η p m r T) s θ=
      ((preferredTermDerivative a T).map (fun U => preferredTermValue τ η p m r U s θ)).sum := by
  induction T with
  | nil =>
    cases a <;> simp [preferredTermValue,preferredTermDerivative,preferredFrameStep,
      preferredParameterFrame,preferredCoordinateFrame]
  | cons x xs ih =>
    have hx := hA x (s,θ) hz
    have ht := preferredTermValue_mixed τ η p m r Ω hA xs (s,θ) hz
    change preferredFrameStep τ p m a
      (fun t y => preferredAtomValue τ η p m r x t y*preferredTermValue τ η p m r xs t y) s θ=_
    rw [preferredFrameStep_mul τ p m a _ _ s θ hx.2 ht.2
      (preferredMixed_coordinate_differentiable _ s θ hx.1)
      (preferredMixed_coordinate_differentiable _ s θ ht.1),preferredAtomValue_shift,ih]
    simp only [preferredTermDerivative,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      preferredTermValue,List.prod_cons,List.sum_map_mul_left]

theorem preferredTermTransport_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => preferredAtomValue τ η p m r a z.1 z.2) Ω)
    (T : PreferredCoefficientTerm N) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportStep τ p m (preferredTermValue τ η p m r T) s θ=
      ((preferredTermTransport T).map (fun U => preferredTermValue τ η p m r U s θ)).sum := by
  change preferredFrameStep τ p m none (preferredTermValue τ η p m r T) s θ+
    (∑ a, preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) a*
      preferredFrameStep τ p m (some a) (preferredTermValue τ η p m r T) s θ)+
    (∑ a, preferredAtomValue τ η p m r (.collective a [some a]) s θ)*
      preferredTermValue τ η p m r T s θ=_
  simp_rw [preferredTermDerivative_identity τ η p m r Ω hA _ T s θ hz]
  simp only [preferredTermTransport,List.map_append,List.sum_append,list_sum_map_flatMap,
    List.map_map,Function.comp_def,preferredTermValue,List.map_cons,List.prod_cons,
    List.sum_map_mul_left,Finset.sum_map_toList,Finset.sum_mul]
  rfl

theorem preferredTermMark_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (T : PreferredCoefficientTerm N) (ij : Fin N × Fin N) (s : ℂ) (θ : Fin N → ℝ)
    (hs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s)
    (hθ : ∀ i, DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i)) :
    preferredTermValue τ η p m r T s θ*preferredKernelMaterialEntry τ p m s θ ij=
      ((preferredTermMark ij T).map (fun U => preferredTermValue τ η p m r U s θ)).sum := by
  rw [preferredKernelMaterialEntry_eq_frames τ p m s θ ij hs hθ]
  simp only [preferredTermMark,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
    preferredTermValue,List.prod_cons,Finset.sum_map_toList,mul_add,Finset.mul_sum]
  congr 1
  · rw [mul_comm]
    rfl
  · apply Finset.sum_congr rfl
    intro a _
    simp only [preferredAtomValue,preferredFrameJet,preferredFrameStep]
    ring

/-- Exact actual scalar coefficient expansion into source jets. No norm
estimate or relation for a generated coefficient is an input hypothesis. -/
theorem preferredWordCoefficient_eq_terms {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => preferredAtomValue τ η p m r a z.1 z.2) Ω)
    (j : ℕ) (w : PreferredMarkedWord N j) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredWordCoefficient τ η p m r j w s θ=
      ((preferredCoefficientTerms j w).map (fun T => preferredTermValue τ η p m r T s θ)).sum := by
  induction j generalizing s θ with
  | zero => simp [preferredWordCoefficient,preferredCoefficientTerms,preferredTermValue,preferredAtomValue,preferredFrameJet]
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simp only [preferredWordCoefficient,preferredCoefficientTerms,hw]
      rw [preferredRegularTransportStep_congr_open τ p m _
        (fun t x => ((preferredCoefficientTerms j (Fin.tail w)).map
          (fun T => preferredTermValue τ η p m r T t x)).sum) Ω hΩ
        (fun z hz => ih (Fin.tail w) z.1 z.2 hz) s θ hz]
      rw [preferredRegularTransportStep_list_sum τ p m (preferredTermValue τ η p m r)
        _ Ω (fun T _ => preferredTermValue_mixed τ η p m r Ω hA T) s θ hz,
        list_sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact preferredTermTransport_identity τ η p m r Ω hA T s θ hz
    | some ij =>
      have hK (a b : Fin N) := hA (.kernel (a,b) []) (s,θ) hz
      have hs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s := by
        apply differentiableAt_pi.mpr
        intro a
        apply differentiableAt_pi.mpr
        intro b
        exact (hK a b).2
      have hθ' (i : Fin N) : DifferentiableAt ℝ
          (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i) := by
        apply differentiableAt_pi.mpr
        intro a
        apply differentiableAt_pi.mpr
        intro b
        exact preferredMixed_coordinate_differentiable _ s θ (hK a b).1 i
      simp only [preferredWordCoefficient,preferredCoefficientTerms,hw]
      rw [ih (Fin.tail w) s θ hz,list_sum_map_flatMap,←List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact preferredTermMark_identity τ η p m r T ij s θ hs hθ'

end
end IsingBulk.Preferred22
