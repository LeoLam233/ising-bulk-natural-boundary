import IsingBulk.Analysis.LieRegularity
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Source-facing fixed-domain differentiation, rc4 Appendix D, lem:lie.
The coordinate volume form is dx₀ ∧ ... ∧ dxₙ. A top form is represented
by its coefficient; contraction and exterior differentiation retain their
alternating signs. All parameter-dependent coefficients remain inside
`lieStep` at every iteration. -/
namespace IsingBulk.Lie
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff

abbrev CoordinateTopForm (n : ℕ) := AngularSpace n → ℂ

def coordinateContraction {n : ℕ} (V : AngularSpace n → Fin (n+1) → ℂ)
    (A : CoordinateTopForm n) (x : AngularSpace n) (i : Fin (n+1)) : ℂ :=
  if Even i.val then V x i * A x else -(V x i * A x)

def coordinateExteriorDerivative {n : ℕ}
    (form : AngularSpace n → Fin (n+1) → ℂ) (x : AngularSpace n) : ℂ :=
  ∑ i, if Even i.val then fderiv ℝ (fun y => form y i) x (Pi.single i 1)
    else -fderiv ℝ (fun y => form y i) x (Pi.single i 1)

def coordinateLieDerivative {n : ℕ} (V : AngularSpace n → Fin (n+1) → ℂ)
    (A : CoordinateTopForm n) : CoordinateTopForm n :=
  coordinateExteriorDerivative (coordinateContraction V A)

theorem coordinateLieDerivative_eq_divergence {n : ℕ}
    (V : AngularSpace n → Fin (n+1) → ℂ) (A : CoordinateTopForm n) :
    coordinateLieDerivative V A = divergence (fun x i => V x i * A x) := by
  funext x
  unfold coordinateLieDerivative coordinateExteriorDerivative divergence
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Even i.val <;> simp [coordinateContraction, h]

theorem lieStep_eq_parameter_sub_Lie {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → CoordinateTopForm n)
    (s : ℂ) (x : AngularSpace n) :
    lieStep V A s x = deriv (fun t => A t x) s - coordinateLieDerivative (V s) (A s) x := by
  rw [coordinateLieDerivative_eq_divergence]
  rfl

theorem positive_dimension_iff_successor (N : ℕ) : 0 < N ↔ ∃ n, N = n+1 := by
  constructor
  · intro h
    exact ⟨N-1, by omega⟩
  · rintro ⟨n, rfl⟩
    omega

/-- The source's fixed real weight is explicit in the density. The hypotheses
are finite-stage regularity, periodic boundary identification and actual
puncture flux, never the desired derivative identity. -/
theorem fixed_domain_lie {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A : ℂ → CoordinateTopForm n) (j : ℕ)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hr : ∀ k < j, StageRegularity T U V ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)))
    (hp : ∀ k < j, ∀ s ∈ U, ∀ i x,
      V s (i.insertNth (T.upper i) x) i *
          ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.upper i) x) =
      V s (i.insertNth (T.lower i) x) i *
          ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.lower i) x))
    (hf : ∀ k < j, ∀ s ∈ U, T.VanishingFlux (fun x i => V s x i *
      ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s x)) :
    EqOn (deriv^[j] (fun s => ∫ x, (w x : ℂ) * A s x ∂T.measure))
      (fun s => ∫ x, ((lieStep V)^[j] (fun t y => (w y : ℂ) * A t y)) s x ∂T.measure) U := by
  exact (iterate_lieStep_integral_on T.measure V _ U hU j
    (fun k hk s hs => (hr k hk).differentiationData hU hs)
    (fun k hk s hs => (hr k hk).fluxExhaustion hV hs (hp k hk s hs) (hf k hk s hs))
    (fun k hk s hs => (hr k hk).divergence_integrable s hs)).symm

/-- Source cutoff rule under its smooth real-weight hypothesis. Smoothness
is only in the real angular variables. -/
theorem fixed_weight_cutoff {n : ℕ} (T : PuncturedTorus n)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A : ℂ → CoordinateTopForm n) (hw : ContDiffOn ℝ ∞ w T.regular)
    (s : ℂ) (x : AngularSpace n) (hx : x ∈ T.regular)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : DifferentiableAt ℝ (A s) x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x) :
    lieStep V (fun t y => (w y : ℂ) * A t y) s x =
      (w x : ℂ) * lieStep V A s x -
      (∑ i, V s x i * (fderiv ℝ w x (Pi.single i 1) : ℂ)) * A s x :=
  lieStep_real_weight V w A s x
    ((hw.differentiableOn (by simp) x hx).differentiableAt (T.regular_open.mem_nhds hx))
    hAs hAx hV

/-- Kernel clause on exactly the regular locus used by the integral. The
factorization is allowed to hold only there; extensions through poles are
irrelevant by locality of the differential operator. -/
theorem fixed_domain_lie_kernel {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A B Y Z : ℂ → CoordinateTopForm n) (j : ℕ)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hK : FrozenKernel U T.regular V Y Z)
    (hfactor : ∀ s ∈ U, ∀ x ∈ T.regular, A s x = simpleKernel Y Z s x * B s x)
    (hBs : ∀ k < j, ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℂ
      (fun t => ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) t x) s)
    (hBx : ∀ k < j, ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℝ
      (((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s) x) :
    ∀ k ≤ j, ∀ s ∈ U, ∀ x ∈ T.regular,
      ((lieStep V)^[k] (fun t y => (w y : ℂ) * A t y)) s x =
        simpleKernel Y Z s x * ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s x := by
  intro k hk s hs x hx
  have he : ∀ t ∈ U, EqOn (fun y => (w y : ℂ) * A t y)
      (fun y => simpleKernel Y Z t y * ((w y : ℂ) * B t y)) T.regular := by
    intro t ht y hy
    dsimp only
    rw [hfactor t ht y hy]
    ring
  rw [iterate_lieStep_congr_on V hU T.regular_open he k s hs hx]
  exact iterate_lieStep_mul_frozen_on V (simpleKernel Y Z) _ U T.regular hU T.regular_open
    (fun _ hs _ hx => hK.parameter hs hx) (fun _ hs _ hx => hK.spatial hs hx) hV
    (fun _ hs _ hx => hK.transport_zero hs hx) k
    (fun l hl => hBs l (by omega)) (fun l hl => hBx l (by omega)) s hs x hx

/-- The kernel clause uses the same full-density regularity as the integral
clause. Generated numerator regularity is not an extra caller assumption. -/
theorem fixed_domain_lie_kernel_of_regular {n : ℕ} (T : PuncturedTorus n)
    (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A B Y Z : ℂ → CoordinateTopForm n) (j : ℕ)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hr : ∀ k < j, StageRegularity T U V ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)))
    (hK : FrozenKernel U T.regular V Y Z)
    (hfactor : ∀ s ∈ U, ∀ x ∈ T.regular, A s x = simpleKernel Y Z s x * B s x) :
    ∀ k ≤ j, ∀ s ∈ U, ∀ x ∈ T.regular,
      ((lieStep V)^[k] (fun t y => (w y : ℂ) * A t y)) s x =
        simpleKernel Y Z s x * ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s x := by
  intro k hk
  apply iterate_lieStep_factor_from_full V (simpleKernel Y Z) _ _ U T.regular hU T.regular_open
    (fun _ hs _ hx => hK.parameter hs hx) (fun _ hs _ hx => hK.spatial hs hx)
    (fun _ hs _ hx => hK.nonzero hs hx) hV (fun _ hs _ hx => hK.transport_zero hs hx)
  · intro s hs x hx
    rw [hfactor s hs x hx]
    ring
  · intro l hl
    exact (hr l (by omega)).parameter
  · intro l hl
    exact (hr l (by omega)).spatial

/-- All iterated integrals in the endpoint are Bochner integrals of integrable
densities, including the last stage. -/
theorem lie_stages_integrable {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → CoordinateTopForm n) (j : ℕ)
    (hA : ∀ s ∈ U, Integrable (A s) T.measure)
    (hr : ∀ k < j, StageRegularity T U V ((lieStep V)^[k] A)) :
    ∀ k ≤ j, ∀ s ∈ U, Integrable (((lieStep V)^[k] A) s) T.measure := by
  intro k hk s hs
  cases k with
  | zero => exact hA s hs
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact (hr k (by omega)).lieStep_integrable hU hs

/-- Bundled source endpoint for rc4 `lem:lie` (manuscript lines 2186–2207).
The clauses give the integral identity, well-definedness at every stage,
the fixed real cutoff rule, and local preservation of both simple kernels.
The only vanishing assumption is on the actual geometric puncture flux. -/
theorem lemma_lie {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A : ℂ → CoordinateTopForm n) (j : ℕ)
    (hw : ContDiffOn ℝ ∞ w T.regular)
    (hAs : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℝ (A s) x)
    (hAi : ∀ s ∈ U, Integrable (fun x => (w x : ℂ) * A s x) T.measure)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hr : ∀ k < j, StageRegularity T U V ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)))
    (hp : ∀ k < j, ∀ s ∈ U, ∀ i x,
      V s (i.insertNth (T.upper i) x) i *
          ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.upper i) x) =
      V s (i.insertNth (T.lower i) x) i *
          ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.lower i) x))
    (hf : ∀ k < j, ∀ s ∈ U, T.VanishingFlux (fun x i => V s x i *
      ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s x)) :
    EqOn (deriv^[j] (fun s => ∫ x, (w x : ℂ) * A s x ∂T.measure))
      (fun s => ∫ x, ((lieStep V)^[j] (fun t y => (w y : ℂ) * A t y)) s x ∂T.measure) U ∧
    (∀ k ≤ j, ∀ s ∈ U, Integrable
      (((lieStep V)^[k] (fun t y => (w y : ℂ) * A t y)) s) T.measure) ∧
    (∀ s ∈ U, ∀ x ∈ T.regular,
      lieStep V (fun t y => (w y : ℂ) * A t y) s x =
        (w x : ℂ) * lieStep V A s x -
        (∑ i, V s x i * (fderiv ℝ w x (Pi.single i 1) : ℂ)) * A s x) ∧
    (∀ B Y Z : ℂ → CoordinateTopForm n, FrozenKernel U T.regular V Y Z →
      (∀ s ∈ U, ∀ x ∈ T.regular, A s x = simpleKernel Y Z s x * B s x) →
      ∀ k ≤ j, ∀ s ∈ U, ∀ x ∈ T.regular,
        ((lieStep V)^[k] (fun t y => (w y : ℂ) * A t y)) s x =
          simpleKernel Y Z s x * ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s x) := by
  refine ⟨fixed_domain_lie T U hU V w A j hV hr hp hf,
    lie_stages_integrable T U hU V _ j hAi hr, ?_, ?_⟩
  · intro s hs x hx
    exact fixed_weight_cutoff T V w A hw s x hx (hAs s hs x hx) (hAx s hs x hx) (hV s hs x hx)
  · intro B Y Z hK hfactor
    exact fixed_domain_lie_kernel_of_regular T U hU V w A B Y Z j hV hr hK hfactor

end
end IsingBulk.Lie
