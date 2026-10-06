import IsingBulk.First.ComplementUniform

/-! Joint smoothness of the actual normalized transpose family, via angular
slices of a real parameter-space function. Parameter cutoffs are not differentiated. -/
namespace IsingBulk.First
noncomputable section
open scoped Topology ContDiff

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Differentiating an angular slice is exactly the joint derivative in (0,e). -/
theorem phaseDirection_slice (e : E) {g : P × E → ℂ}
    (hg : ContDiff ℝ ∞ g) (p : P) (x : E) :
    phaseDirection e (fun y => g (p, y)) x = phaseDirection (0, e) g (p, x) := by
  have hc : HasFDerivAt (fun y : E => (p, y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  have h := (hg.differentiable (by simp) (p, x)).hasFDerivAt.comp x hc
  unfold phaseDirection
  simpa [Function.comp_def] using congrArg (fun L : E →L[ℝ] ℂ => L e) h.fderiv

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
/-- Restricting to a fixed parameter cannot create angular support away from
the joint support. -/
theorem slice_tsupport_subset {A : P × E → ℂ} (p : P) {x : E}
    (hx : x ∈ tsupport (fun y => A (p, y))) : (p, x) ∈ tsupport A := by
  exact tsupport_comp_subset_preimage (f := fun y : E => (p, y)) A (by fun_prop) hx

/-- The true transpose commutes with fixing the external parameters. -/
theorem phaseTranspose_slice (e : E) {g A : P × E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A)
    (hne : ∀ z ∈ tsupport A, phaseDirection (0, e) g z ≠ 0) (p : P) :
    phaseTranspose e (fun y => g (p, y)) (fun y => A (p, y)) =
      fun x => phaseTranspose (0, e) g A (p, x) := by
  let Q : P × E → ℂ := fun z => A z / phaseDirection (0, e) g z
  have hQ : ContDiff ℝ ∞ Q := contDiff_quotient_of_support A (phaseDirection (0, e) g)
    hA (contDiff_phaseDirection (0, e) hg) hne
  have heq : (fun y => A (p, y) / phaseDirection e (fun y => g (p, y)) y) =
      fun y => Q (p, y) := by
    funext y
    rw [phaseDirection_slice e hg]
  funext x
  unfold phaseTranspose
  rw [heq]
  exact congrArg Neg.neg (phaseDirection_slice e hQ p x)

/-- Every actual q-fold angular transpose is the slice of the joint q-fold
transpose. In particular, all coefficient derivatives retain parameter dependence. -/
theorem phaseTransposeIter_slice (e : E) {g A : P × E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ z ∈ tsupport A, phaseDirection (0, e) g z ≠ 0) (p : P) (q : ℕ) :
    phaseTransposeIter e (fun y => g (p, y)) (fun y => A (p, y)) q =
      fun x => phaseTransposeIter (0, e) g A q (p, x) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change phaseTranspose e (fun y => g (p, y))
      (phaseTransposeIter e (fun y => g (p, y)) (fun y => A (p, y)) q) = _
    rw [ih]
    have hr := phaseTransposeIter_regularity (0, e) hg hA hc hne q
    exact phaseTranspose_slice e hg hr.1 (fun z hz => hne z (hr.2.2 hz)) p

/-- The joint-continuity hypothesis in uniform_nonstationary_decay is derived
for this globally extended, compactly parameter-localized source family. -/
theorem contDiff_parameterized_transpose (e : E) {g A : P × E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hne : ∀ z ∈ tsupport A, phaseDirection (0, e) g z ≠ 0) (q : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E =>
      phaseTransposeIter e (fun y => g (z.1, y)) (fun y => A (z.1, y)) q z.2) := by
  have heq : (fun z : P × E =>
      phaseTransposeIter e (fun y => g (z.1, y)) (fun y => A (z.1, y)) q z.2) =
      phaseTransposeIter (0, e) g A q := by
    funext z
    exact congrFun (phaseTransposeIter_slice e hg hA hc hne z.1 q) z.2
  rw [heq]
  exact (phaseTransposeIter_regularity (0, e) hg hA hc hne q).1

end
end IsingBulk.First
