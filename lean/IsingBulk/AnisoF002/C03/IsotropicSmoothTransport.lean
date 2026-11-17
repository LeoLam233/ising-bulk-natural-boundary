import IsingBulk.AnisoF002.C03.IsotropicFrozenKernelCurrent

/-!
# Smooth transport with every amplitude derivative retained

The regular transport operator acts on the actual parameter-dependent
amplitude. Its iterates are genuine smooth functions away from the total
diagonal, so the exact current can be reapplied without discarding any
derivative of a coefficient, cutoff, or previous descendant.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix ContDiff
open Set Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarPartial_contDiffAt (f : E → ℂ) (v x : E)
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (scalarPartial f v) x := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

omit [DecidableEq ι] in
theorem scalarCoordinateMatrix_contDiffAt (χ : ι → E → ℂ) (e : ι → E) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x) :
    ContDiffAt ℝ ∞ (scalarCoordinateMatrix χ e) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact scalarPartial_contDiffAt (χ i) (e j) x (hχ i)

theorem scalarMatrixDet_contDiffAt (M : E → ι → ι → ℂ) (x : E)
    (hM : ContDiffAt ℝ ∞ M x) : ContDiffAt ℝ ∞ (fun y => Matrix.det (M y)) x := by
  have he : (fun y => Matrix.det (M y)) =
      (fun y => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℂ) * ∏ i, M y (σ i) i) :=
    funext (fun y => Matrix.det_apply' (M y))
  rw [he]
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod (fun i _ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hM (σ i)) i))

theorem scalarInverseEntry_contDiffAt (M : E → ι → ι → ℂ) (x : E)
    (hM : ContDiffAt ℝ ∞ M x) (hdet : Matrix.det (M x) ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => scalarInverseEntry (M y) i j) x := by
  have hu : ContDiffAt ℝ ∞
      (fun y k l => Matrix.updateRow (M y) j (Pi.single i 1) k l) x := by
    apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_pi.mpr
    intro l
    have he : (fun y => Matrix.updateRow (M y) j (Pi.single i 1) k l) =
        (fun y => if k = j then (Pi.single i 1 : ι → ℂ) l else M y k l) :=
      funext (fun _ => Matrix.updateRow_apply)
    rw [he]
    by_cases h : k = j
    · subst k
      simpa only [ite_true] using
        (contDiffAt_const (𝕜 := ℝ) (x := x) (n := ∞) (c := ((Pi.single i 1 : ι → ℂ) l)))
    · simpa only [ite_eq_right h] using
        (contDiffAt_pi.mp (contDiffAt_pi.mp hM k) l)
  have he : (fun y => scalarInverseEntry (M y) i j) =
      (fun y => (Matrix.det (M y))⁻¹ * (Matrix.updateRow (M y) j (Pi.single i 1)).det) :=
    funext (fun y => scalarInverseEntry_eq (M y) i j)
  rw [he]
  exact ((scalarMatrixDet_contDiffAt M x hM).inv hdet).mul
    (scalarMatrixDet_contDiffAt _ x hu)

theorem scalarRegularFrameDerivative_contDiffAt (χ : ι → E → ℂ) (e : ι → E)
    (b : E → ℂ) (i : ι) (x : E)
    (hχ : ∀ j, ContDiffAt ℝ ∞ (χ j) x) (hb : ContDiffAt ℝ ∞ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    ContDiffAt ℝ ∞ (scalarRegularFrameDerivative χ e b i) x := by
  change ContDiffAt ℝ ∞ (fun y => ∑ l,
    scalarInverseEntry (scalarCoordinateMatrix χ e y) l i * scalarPartial b (e l) y) x
  apply ContDiffAt.sum
  intro l _
  exact (scalarInverseEntry_contDiffAt _ x (scalarCoordinateMatrix_contDiffAt χ e x hχ)
    hdet l i).mul (scalarPartial_contDiffAt b (e l) x hb)

theorem scalarRegularParameterDerivative_contDiffAt (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (b : E → ℂ) (x : E)
    (hχ : ∀ j, ContDiffAt ℝ ∞ (χ j) x) (hb : ContDiffAt ℝ ∞ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    ContDiffAt ℝ ∞ (scalarRegularParameterDerivative χ e a b) x := by
  change ContDiffAt ℝ ∞ (fun y => scalarPartial b a y -
    ∑ l, (∑ j, scalarInverseEntry (scalarCoordinateMatrix χ e y) l j *
      scalarPartial (χ j) a y) * scalarPartial b (e l) y) x
  apply (scalarPartial_contDiffAt b a x hb).sub
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul _ (scalarPartial_contDiffAt b (e l) x hb)
  apply ContDiffAt.sum
  intro j _
  exact (scalarInverseEntry_contDiffAt _ x (scalarCoordinateMatrix_contDiffAt χ e x hχ)
    hdet l j).mul (scalarPartial_contDiffAt (χ j) a x (hχ j))

theorem regularTransportAmplitude_contDiffAt (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    ContDiffAt ℝ ∞ (regularTransportAmplitude χ e a B b) x := by
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · exact scalarRegularParameterDerivative_contDiffAt χ e a b x hχ hb hdet
    · apply ContDiffAt.sum
      intro i _
      exact (hB i).mul (scalarRegularFrameDerivative_contDiffAt χ e b i x hχ hb hdet)
  · apply ContDiffAt.mul _ hb
    apply ContDiffAt.sum
    intro i _
    exact scalarRegularFrameDerivative_contDiffAt χ e (B i) i x hχ (hB i) hdet

/-- The complete transport recurrence; each step differentiates the
entire preceding amplitude, including all of its parameter dependence. -/
noncomputable def regularTransportDescendant (χ : ι → E → ℂ) (e : ι → E) (a : E)
    (B : ι → E → ℂ) (b : E → ℂ) : ℕ → E → ℂ
  | 0 => b
  | n + 1 => regularTransportAmplitude χ e a B (regularTransportDescendant χ e a B b n)

theorem regularTransportDescendant_contDiffAt (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) (n : ℕ) :
    ContDiffAt ℝ ∞ (regularTransportDescendant χ e a B b n) x := by
  induction n with
  | zero => exact hb
  | succ n ih => exact regularTransportAmplitude_contDiffAt χ e a x B _ hχ hB ih hdet

end IsingBulk.AnisoF002.Isotropic
