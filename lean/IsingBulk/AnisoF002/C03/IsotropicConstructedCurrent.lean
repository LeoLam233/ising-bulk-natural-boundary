import IsingBulk.AnisoF002.C03.IsotropicRegularFrameCurrent

/-!
# A constructed angular velocity and its exact scalar current

The velocity is formed by the inverse of the actual coordinate matrix.
Its differentiability is proved from the adjugate formula, and the
regular transport field is recovered exactly on a neighborhood. Thus
the current requires only C² coordinates and a C¹ regular field.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarInverseEntry (M : Matrix ι ι ℂ) (i j : ι) : ℂ := M⁻¹ i j

def scalarInverseAction (M : Matrix ι ι ℂ) (v : ι → ℂ) : ι → ℂ := M⁻¹ *ᵥ v

theorem scalarInverseEntry_eq (M : Matrix ι ι ℂ) (i j : ι) :
    scalarInverseEntry M i j = M.det⁻¹ * (Matrix.updateRow M j (Pi.single i 1)).det := by
  rw [scalarInverseEntry, Matrix.inv_def, Ring.inverse_eq_inv]
  change M.det⁻¹ * M.adjugate i j = _
  rw [Matrix.adjugate_apply]

theorem scalarMatrixDet_differentiableAt (M : E → ι → ι → ℂ) (x : E)
    (hM : DifferentiableAt ℝ M x) : DifferentiableAt ℝ (fun y => Matrix.det (M y)) x := by
  exact ((((scalarDeterminant (ι := ι)).restrictScalars ℝ).hasFDerivAt (M x)).comp x
    hM.hasFDerivAt).differentiableAt

theorem scalarInverseEntry_differentiableAt (M : E → ι → ι → ℂ) (x : E)
    (hM : DifferentiableAt ℝ M x) (hdet : Matrix.det (M x) ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun y => scalarInverseEntry (M y) i j) x := by
  have hu : DifferentiableAt ℝ
      (fun y k l => Matrix.updateRow (M y) j (Pi.single i 1) k l) x := by
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro l
    have he : (fun y => Matrix.updateRow (M y) j (Pi.single i 1) k l) =
        (fun y => if k = j then (Pi.single i 1 : ι → ℂ) l else M y k l) :=
      funext (fun _ => Matrix.updateRow_apply)
    rw [he]
    by_cases h : k = j
    · subst k
      simpa only [ite_true] using
        (differentiableAt_const (𝕜 := ℝ) (x := x) ((Pi.single i 1 : ι → ℂ) l))
    · simpa only [ite_eq_right h] using
        (differentiableAt_pi.mp (differentiableAt_pi.mp hM k) l)
  have he : (fun y => scalarInverseEntry (M y) i j) =
      (fun y => (Matrix.det (M y))⁻¹ * (Matrix.updateRow (M y) j (Pi.single i 1)).det) :=
    funext (fun y => scalarInverseEntry_eq (M y) i j)
  rw [he]
  exact ((scalarMatrixDet_differentiableAt M x hM).inv hdet).mul
    (scalarMatrixDet_differentiableAt _ x hu)

def constructedAngularVelocity (χ : ι → E → ℂ) (e : ι → E) (a : E)
    (B : ι → E → ℂ) (i : ι) (x : E) : ℂ :=
  scalarInverseAction (scalarCoordinateMatrix χ e x)
    (fun j => scalarPartial (χ j) a x - B j x) i

theorem constructedAngularVelocity_differentiableAt (χ : ι → E → ℂ) (e : ι → E)
    (a x : E) (B : ι → E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hB : ∀ i, DifferentiableAt ℝ (B i) x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) (i : ι) :
    DifferentiableAt ℝ (constructedAngularVelocity χ e a B i) x := by
  change DifferentiableAt ℝ (fun y => ∑ j, scalarInverseEntry (scalarCoordinateMatrix χ e y) i j *
    (scalarPartial (χ j) a y - B j y)) x
  apply DifferentiableAt.fun_sum
  intro j _
  exact (scalarInverseEntry_differentiableAt _ x
    (scalarCoordinateMatrix_differentiableAt χ e x hχ) hdet i j).mul
    ((scalarPartial_differentiableAt (χ j) a x (hχ j)).sub (hB j))

theorem constructedAngularVelocity_transport (χ : ι → E → ℂ) (e : ι → E)
    (a x : E) (B : ι → E → ℂ) (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarTransportVelocity χ e a (constructedAngularVelocity χ e a B) x = fun i => B i x := by
  let M : Matrix ι ι ℂ := scalarCoordinateMatrix χ e x
  let u : ι → ℂ := fun i => scalarPartial (χ i) a x
  let b : ι → ℂ := fun i => B i x
  have he : M *ᵥ (M⁻¹ *ᵥ (u - b)) = u - b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  change u - M *ᵥ (M⁻¹ *ᵥ (u - b)) = b
  rw [he]
  abel

/-- An actual constructed current, for an arbitrary differentiable
amplitude on the original real coordinate space. -/
theorem exact_constructed_regular_current (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hB : ∀ i, DifferentiableAt ℝ (B i) x) (hb : DifferentiableAt ℝ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarPartial (fun y => scalarCoordinateDet χ e y * b y) a x -
        (∑ i, scalarPartial (fun y => constructedAngularVelocity χ e a B i y *
          scalarCoordinateDet χ e y * b y) (e i) x) =
      scalarCoordinateDet χ e x *
        (scalarRegularParameterDerivative χ e a b x +
          (∑ i, B i x * scalarRegularFrameDerivative χ e b i x) +
          (∑ i, scalarRegularFrameDerivative χ e (B i) i x) * b x) := by
  have hV := constructedAngularVelocity_differentiableAt χ e a x B hχ hB hdet
  have hcurrent := exact_regular_frame_current χ e a x
    (constructedAngularVelocity χ e a B) b hχ hV hb hdet
  have he : ∀ᶠ y in 𝓝 x, scalarTransportVelocity χ e a
      (constructedAngularVelocity χ e a B) y = fun i => B i y := by
    filter_upwards [(scalarCoordinateDet_differentiableAt χ e x hχ).continuousAt.eventually_ne hdet]
      with y hy
    exact constructedAngularVelocity_transport χ e a y B hy
  have he0 := constructedAngularVelocity_transport χ e a x B hdet
  have heD (i : ι) : scalarRegularFrameDerivative χ e
      (fun y => scalarTransportVelocity χ e a (constructedAngularVelocity χ e a B) y i) i x =
      scalarRegularFrameDerivative χ e (B i) i x := by
    have hei : (fun y => scalarTransportVelocity χ e a (constructedAngularVelocity χ e a B) y i)
        =ᶠ[𝓝 x] B i := he.mono (fun y hy => congrFun hy i)
    simp only [scalarRegularFrameDerivative, scalarFrameApplied, scalarPartial, hei.fderiv_eq]
  simpa only [he0, heD] using hcurrent

end IsingBulk.AnisoF002.Isotropic
