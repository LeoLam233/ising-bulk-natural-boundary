import IsingBulk.HT22.Tail.FrameCalculus
import IsingBulk.Preferred22.CoefficientCalculus

/-! # Actual new-field coefficients as source-jet differential polynomials

The abstract atom grammar, product-rule term lists, and their loss/count
proofs are shared. Their evaluator is not: it uses actual fixed-v HT22
frames, the new mixed residual, and the ordinary odd bordered kernel.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def atomValue {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (a : PreferredCoefficientAtom N) : ℂ → (Fin N → ℝ) → ℂ :=
  match a with
  | .seed xs => frameJet τ p m (regularSeedCoefficient τ η p m r) xs
  | .collective i xs => frameJet τ p m
      (fun s θ => residualField s (sourceCoordinate τ p m s θ) i) xs
  | .kernel ij xs => frameJet τ p m
      (fun s θ => sourceOrdinaryKernel τ p m s θ ij.1 ij.2) xs

def termValue {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (T : PreferredCoefficientTerm N) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (T.map (fun a => atomValue τ η p m r a s θ)).prod

theorem atomValue_shift {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    frameStep τ p m a (atomValue τ η p m r x)=
      atomValue τ η p m r (preferredAtomShift a x) := by
  cases x <;> cases a <;> rfl

theorem atomValue_mixed {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (a : PreferredCoefficientAtom N) :
    PreferredMixedSmoothOn (fun z => atomValue τ η p m r a z.1 z.2) Ω := by
  cases a with
  | seed xs =>
    exact frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR _
      (regularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint) xs
  | collective i xs =>
    apply frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR _ _ xs
    exact (source_generator_factors_mixed τ δ p m hp hm Ω hpoint hR).2.2.2 i
  | kernel ij xs =>
    exact frameJet_mixed τ δ p m hp hm Ω hΩ hpoint hR _
      (sourceOrdinaryKernel_mixed τ δ p m hp hm Ω hpoint ij) xs

theorem termValue_mixed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => atomValue τ η p m r a z.1 z.2) Ω)
    (T : PreferredCoefficientTerm N) :
    PreferredMixedSmoothOn (fun z => termValue τ η p m r T z.1 z.2) Ω :=
  PreferredMixedSmoothOn.list_prod _ T Ω (fun a _ => hA a)

theorem termDerivative_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => atomValue τ η p m r a z.1 z.2) Ω)
    (a : Option (Fin N)) (T : PreferredCoefficientTerm N)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameStep τ p m a (termValue τ η p m r T) s θ=
      ((preferredTermDerivative a T).map (fun U => termValue τ η p m r U s θ)).sum := by
  induction T with
  | nil =>
    cases a <;> simp [termValue,preferredTermDerivative,frameStep,
      parameterFrame,coordinateFrame]
  | cons x xs ih =>
    have hx := hA x (s,θ) hz
    have ht := termValue_mixed τ η p m r Ω hA xs (s,θ) hz
    change frameStep τ p m a
      (fun t y => atomValue τ η p m r x t y*termValue τ η p m r xs t y) s θ=_
    rw [frameStep_mul τ p m a _ _ s θ hx.2 ht.2
      (preferredMixed_coordinate_differentiable _ s θ hx.1)
      (preferredMixed_coordinate_differentiable _ s θ ht.1),atomValue_shift,ih]
    simp only [preferredTermDerivative,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      termValue,List.prod_cons,List.sum_map_mul_left]

theorem termTransport_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => atomValue τ η p m r a z.1 z.2) Ω)
    (T : PreferredCoefficientTerm N) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportStep τ p m (termValue τ η p m r T) s θ=
      ((preferredTermTransport T).map (fun U => termValue τ η p m r U s θ)).sum := by
  change frameStep τ p m none (termValue τ η p m r T) s θ+
    (∑ a, residualField s (sourceCoordinate τ p m s θ) a*
      frameStep τ p m (some a) (termValue τ η p m r T) s θ)+
    (∑ a, atomValue τ η p m r (.collective a [some a]) s θ)*
      termValue τ η p m r T s θ=_
  simp_rw [termDerivative_identity τ η p m r Ω hA _ T s θ hz]
  simp only [preferredTermTransport,List.map_append,List.sum_append,list_sum_map_flatMap,
    List.map_map,Function.comp_def,termValue,List.map_cons,List.prod_cons,
    List.sum_map_mul_left,Finset.sum_map_toList,Finset.sum_mul]
  rfl

theorem termMark_identity {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (T : PreferredCoefficientTerm N) (ij : Fin N × Fin N) (s : ℂ) (θ : Fin N → ℝ)
    (hs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t θ) s)
    (hθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m s (Function.update θ i x)) (θ i)) :
    termValue τ η p m r T s θ*ordinaryMaterialEntry τ p m s θ ij=
      ((preferredTermMark ij T).map (fun U => termValue τ η p m r U s θ)).sum := by
  rw [ordinaryMaterialEntry_eq_frames τ p m s θ ij hs hθ]
  simp only [preferredTermMark,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
    termValue,List.prod_cons,Finset.sum_map_toList,mul_add,Finset.mul_sum]
  congr 1
  · rw [mul_comm]
    rfl
  · apply Finset.sum_congr rfl
    intro a _
    simp only [atomValue,frameJet,frameStep]
    ring

/-- Exact actual scalar coefficient expansion into source jets. No norm
estimate or relation for a generated coefficient is an input hypothesis. -/
theorem wordCoefficient_eq_terms {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hA : ∀ a, PreferredMixedSmoothOn (fun z => atomValue τ η p m r a z.1 z.2) Ω)
    (j : ℕ) (w : PreferredMarkedWord N j) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    wordCoefficient τ η p m r j w s θ=
      ((preferredCoefficientTerms j w).map (fun T => termValue τ η p m r T s θ)).sum := by
  induction j generalizing s θ with
  | zero => simp [wordCoefficient,preferredCoefficientTerms,termValue,atomValue,frameJet]
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simp only [wordCoefficient,preferredCoefficientTerms,hw]
      rw [regularTransportStep_congr_open τ p m _
        (fun t x => ((preferredCoefficientTerms j (Fin.tail w)).map
          (fun T => termValue τ η p m r T t x)).sum) Ω hΩ
        (fun z hz => ih (Fin.tail w) z.1 z.2 hz) s θ hz]
      rw [regularTransportStep_list_sum τ p m (termValue τ η p m r)
        _ Ω (fun T _ => termValue_mixed τ η p m r Ω hA T) s θ hz,
        list_sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact termTransport_identity τ η p m r Ω hA T s θ hz
    | some ij =>
      have hK (a b : Fin N) := hA (.kernel (a,b) []) (s,θ) hz
      have hs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t θ) s := by
        apply differentiableAt_pi.mpr
        intro a
        apply differentiableAt_pi.mpr
        intro b
        exact (hK a b).2
      have hθ' (i : Fin N) : DifferentiableAt ℝ
          (fun x => sourceOrdinaryKernel τ p m s (Function.update θ i x)) (θ i) := by
        apply differentiableAt_pi.mpr
        intro a
        apply differentiableAt_pi.mpr
        intro b
        exact preferredMixed_coordinate_differentiable _ s θ (hK a b).1 i
      simp only [wordCoefficient,preferredCoefficientTerms,hw]
      rw [ih (Fin.tail w) s θ hz,list_sum_map_flatMap,←List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact termMark_identity τ η p m r T ij s θ hs hθ'

end
end IsingBulk.HT22.Tail
