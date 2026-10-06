import IsingBulk.Analysis.LieTheorem

/-! Periodic boundary identification is inherited from the original torus
fields. It need not be separately postulated for generated coefficients. -/
namespace IsingBulk.Lie
noncomputable section
open Set Filter
open MeasureTheory
open scoped Topology ContDiff BigOperators

def AngularPeriodic {n : ℕ} {E : Type*} (f : AngularSpace n → E) : Prop :=
  ∀ i x, f (x + Pi.single i (2 * Real.pi)) = f x

theorem angularPeriodic_mul {n : ℕ} {E : Type*} [Mul E]
    {f g : AngularSpace n → E} (hf : AngularPeriodic f) (hg : AngularPeriodic g) :
    AngularPeriodic (fun x => f x * g x) := by
  intro i x
  dsimp only
  rw [hf i x, hg i x]

theorem angularPeriodic_fderiv {n : ℕ} {f : AngularSpace n → ℂ}
    (hf : AngularPeriodic f) : AngularPeriodic (fderiv ℝ f) := by
  intro i x
  rw [← fderiv_comp_add_right]
  have he : (fun y => f (y + Pi.single i (2 * Real.pi))) = f := funext (hf i)
  rw [he]

theorem angularPeriodic_lieStep {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ s ∈ U, AngularPeriodic (V s)) (hA : ∀ s ∈ U, AngularPeriodic (A s))
    {s : ℂ} (hs : s ∈ U) : AngularPeriodic (lieStep V A s) := by
  intro i x
  have he : (fun t => A t (x + Pi.single i (2 * Real.pi))) =ᶠ[𝓝 s] (fun t => A t x) := by
    filter_upwards [hU.mem_nhds hs] with t ht using hA t ht i x
  unfold lieStep divergence
  rw [he.deriv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have hf : AngularPeriodic (fun y => V s y r * A s y) :=
    angularPeriodic_mul (fun i x => congrFun (hV s hs i x) r) (hA s hs)
  rw [angularPeriodic_fderiv hf i x]

theorem angularPeriodic_lie_iterate {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ s ∈ U, AngularPeriodic (V s)) (hA : ∀ s ∈ U, AngularPeriodic (A s))
    (k : ℕ) : ∀ s ∈ U, AngularPeriodic (((lieStep V)^[k] A) s) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    exact angularPeriodic_lieStep hU V _ hV ih hs

theorem angularPeriodic_faces {n : ℕ} {E : Type*} (T : PuncturedTorus n)
    {f : AngularSpace n → E} (hf : AngularPeriodic f) (i : Fin (n+1)) (x : Fin n → ℝ) :
    f (i.insertNth (T.upper i) x) = f (i.insertNth (T.lower i) x) := by
  have he : (i.insertNth (T.upper i) x : AngularSpace n) =
      i.insertNth (T.lower i) x + Pi.single i (2 * Real.pi) := by
    funext r
    rcases i.eq_self_or_eq_succAbove r with rfl | ⟨r, rfl⟩
    · simp [T.period]
    · simp [Fin.succAbove_ne]
  rw [he, hf i]

theorem periodic_stages_face_eq {n : ℕ} (T : PuncturedTorus n) {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A : ℂ → CoordinateTopForm n)
    (hV : ∀ s ∈ U, AngularPeriodic (V s)) (hw : AngularPeriodic w)
    (hA : ∀ s ∈ U, AngularPeriodic (A s)) (k : ℕ) {s : ℂ} (hs : s ∈ U)
    (i : Fin (n+1)) (x : Fin n → ℝ) :
    V s (i.insertNth (T.upper i) x) i *
        ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.upper i) x) =
    V s (i.insertNth (T.lower i) x) i *
        ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s (i.insertNth (T.lower i) x) := by
  apply angularPeriodic_faces T (f := fun y => V s y i *
    ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)) s y) _ i x
  exact angularPeriodic_mul (fun i x => congrFun (hV s hs i x) _)
    (angularPeriodic_lie_iterate hU V _ hV
      (fun s hs => angularPeriodic_mul (fun i x => congrArg Complex.ofReal (hw i x)) (hA s hs)) k s hs)

/-- Source-facing bundled endpoint. Periodicity is assumed only for the
original angular weight, form and field, and is proved for every Lie stage.
Stage regularity and vanishing geometric puncture flux are separate premises. -/
theorem lemma_lie_on_torus {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A : ℂ → CoordinateTopForm n) (j : ℕ)
    (hw : ContDiffOn ℝ ∞ w T.regular)
    (hAs : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℝ (A s) x)
    (hAi : ∀ s ∈ U, Integrable (fun x => (w x : ℂ) * A s x) T.measure)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hVp : ∀ s ∈ U, AngularPeriodic (V s)) (hwp : AngularPeriodic w)
    (hAp : ∀ s ∈ U, AngularPeriodic (A s))
    (hr : ∀ k < j, StageRegularity T U V ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)))
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
          simpleKernel Y Z s x * ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s x) :=
  lemma_lie T U hU V w A j hw hAs hAx hAi hV hr
    (fun k _ _ hs => periodic_stages_face_eq T hU V w A hVp hwp hAp k hs) hf

end
end IsingBulk.Lie
