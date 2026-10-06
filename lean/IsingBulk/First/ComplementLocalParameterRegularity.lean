import IsingBulk.First.ComplementParameterRegularity

/-! Local joint regularity of the normalized transpose, avoiding any global
parameter extension. This is the source-serving compact-family route. -/
namespace IsingBulk.First
noncomputable section
open scoped ContDiff

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Parameterized angular differentiation is jointly smooth locally. -/
theorem contDiffAt_parameterized_direction (e : E) {g : P × E → ℂ} (p : P) (x : E)
    (hg : ContDiffAt ℝ ∞ g (p, x)) :
    ContDiffAt ℝ ∞ (fun z : P × E => phaseDirection e (fun y => g (z.1, y)) z.2) (p, x) := by
  have hunc : ContDiffAt ℝ ∞
      (Function.uncurry (fun z : P × E => fun y : E => g (z.1, y))) ((p, x), x) := by
    exact hg.comp ((p, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd := hunc.fderiv (g := fun z : P × E => z.2) contDiffAt_snd
    (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  exact hd.clm_apply contDiffAt_const

/-- One full transpose is jointly smooth at any point where its actual
phase-direction denominator is nonzero. -/
theorem contDiffAt_parameterized_transpose (e : E) {g A : P × E → ℂ} (p : P) (x : E)
    (hg : ContDiffAt ℝ ∞ g (p, x)) (hA : ContDiffAt ℝ ∞ A (p, x))
    (hne : phaseDirection e (fun y => g (p, y)) x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : P × E =>
      phaseTranspose e (fun y => g (z.1, y)) (fun y => A (z.1, y)) z.2) (p, x) := by
  let Q : P × E → ℂ := fun z => A z / phaseDirection e (fun y => g (z.1, y)) z.2
  have hQ : ContDiffAt ℝ ∞ Q (p, x) := by
    simpa only [Q, div_eq_mul_inv, Pi.inv_apply, Pi.mul_apply] using
      hA.mul ((contDiffAt_parameterized_direction e p x hg).inv hne)
  exact (contDiffAt_parameterized_direction e p x hQ).neg

/-- Arbitrary normalized transpose order has actual local joint C∞ regularity.
No continuity or bound of generated coefficients is taken as an input. -/
theorem contDiffAt_parameterized_transposeIter (e : E) {g A : P × E → ℂ} (p : P) (x : E)
    (hg : ContDiffAt ℝ ∞ g (p, x)) (hA : ContDiffAt ℝ ∞ A (p, x))
    (hne : phaseDirection e (fun y => g (p, y)) x ≠ 0) (q : ℕ) :
    ContDiffAt ℝ ∞ (fun z : P × E =>
      phaseTransposeIter e (fun y => g (z.1, y)) (fun y => A (z.1, y)) q z.2) (p, x) := by
  induction q with
  | zero => exact hA
  | succ q ih => exact contDiffAt_parameterized_transpose e p x hg ih hne

/-- The generated-amplitude continuity condition in the uniform decay theorem
is discharged from ordinary source-local smoothness and the proved separator. -/
theorem continuousOn_parameterized_transposeIter (e : E) {g A : P × E → ℂ}
    (K : Set P) (L : Set E)
    (hg : ∀ p ∈ K, ∀ x ∈ L, ContDiffAt ℝ ∞ g (p, x))
    (hA : ∀ p ∈ K, ∀ x ∈ L, ContDiffAt ℝ ∞ A (p, x))
    (hne : ∀ p ∈ K, ∀ x ∈ L, phaseDirection e (fun y => g (p, y)) x ≠ 0) (q : ℕ) :
    ContinuousOn (fun z : P × E =>
      phaseTransposeIter e (fun y => g (z.1, y)) (fun y => A (z.1, y)) q z.2) (K ×ˢ L) := by
  rintro ⟨p, x⟩ ⟨hp, hx⟩
  exact (contDiffAt_parameterized_transposeIter e p x (hg p hp x hx)
    (hA p hp x hx) (hne p hp x hx) q).continuousAt.continuousWithinAt

end
end IsingBulk.First
