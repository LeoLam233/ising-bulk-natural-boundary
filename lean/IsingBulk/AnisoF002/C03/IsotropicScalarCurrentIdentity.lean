import IsingBulk.AnisoF002.C03.IsotropicScalarCurrent

/-!
# The exact scalar current identity

The coordinate determinant and all derivatives below are genuine real
derivatives of complex scalar functions. The regular velocity is defined
by the coordinate relation. C² symmetry supplies its matrix transport
equation, and the proved Jacobi formula supplies the determinant current.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarRegularDivergence (M DB : Matrix ι ι ℂ) : ℂ := (DB * M⁻¹).trace

theorem scalarDeterminantDerivative_mul_right (M A : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    scalarDeterminantDerivative M (M * A) = A.trace * M.det := by
  rw [scalarDeterminantDerivative_trace M (M * A) hM, Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mul]

theorem determinant_current_matrix_identity (M H DB DV : Matrix ι ι ℂ)
    (V : ι → ℂ) (T : ι → Matrix ι ι ℂ) (hM : M.det ≠ 0)
    (htransport : H = DB + M * DV + ∑ i, V i • T i) :
    scalarDeterminantDerivative M H - (∑ i, V i * scalarDeterminantDerivative M (T i)) -
        M.det * DV.trace = M.det * scalarRegularDivergence M DB := by
  rw [htransport, scalarDeterminantDerivative_add, scalarDeterminantDerivative_add,
    scalarDeterminantDerivative_mul_right M DV hM, scalarDeterminantDerivative_sum]
  simp_rw [scalarDeterminantDerivative_smul]
  rw [scalarDeterminantDerivative_trace M DB hM]
  unfold scalarRegularDivergence
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem scalar_array_fderiv_entry (M : E → ι → ι → ℂ) (x a : E)
    (hM : DifferentiableAt ℝ M x) (i j : ι) :
    fderiv ℝ M x a i j = scalarPartial (fun y => M y i j) a x := by
  have hi : DifferentiableAt ℝ (fun y => M y i) x := differentiableAt_pi.mp hM i
  rw [scalarPartial, fderiv_apply hi j, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    fderiv_apply hM i, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

def scalarCoordinateDet (χ : ι → E → ℂ) (e : ι → E) (x : E) : ℂ :=
  Matrix.det (scalarCoordinateMatrix χ e x)

def scalarTransportDivergence (χ : ι → E → ℂ) (e : ι → E) (a : E)
    (V : ι → E → ℂ) (x : E) : ℂ :=
  scalarRegularDivergence (scalarCoordinateMatrix χ e x)
    (scalarCoordinateMatrix (fun i y => scalarTransportVelocity χ e a V y i) e x)

theorem scalarCoordinateDet_differentiableAt (χ : ι → E → ℂ) (e : ι → E) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x) :
    DifferentiableAt ℝ (scalarCoordinateDet χ e) x := by
  have hd := ((scalarDeterminant (ι := ι)).restrictScalars ℝ).hasFDerivAt
    (scalarCoordinateMatrix χ e x)
  exact (hd.comp x (scalarCoordinateMatrix_differentiableAt χ e x hχ).hasFDerivAt).differentiableAt

/-- The determinant part of the exact current. It is derived from the
actual C² coordinate map and arbitrary C¹ complex angular velocity. -/
theorem scalarCoordinateDet_current (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (V : ι → E → ℂ) (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarPartial (scalarCoordinateDet χ e) a x -
        (∑ i, V i x * scalarPartial (scalarCoordinateDet χ e) (e i) x) -
        scalarCoordinateDet χ e x * (∑ i, scalarPartial (V i) (e i) x) =
      scalarCoordinateDet χ e x * scalarTransportDivergence χ e a V x := by
  let M : Matrix ι ι ℂ := scalarCoordinateMatrix χ e x
  let H : Matrix ι ι ℂ := fderiv ℝ (scalarCoordinateMatrix χ e) x a
  let T : ι → Matrix ι ι ℂ := fun i => fderiv ℝ (scalarCoordinateMatrix χ e) x (e i)
  let DB : Matrix ι ι ℂ :=
    scalarCoordinateMatrix (fun i y => scalarTransportVelocity χ e a V y i) e x
  let DV : Matrix ι ι ℂ := scalarCoordinateMatrix V e x
  have hMd := scalarCoordinateMatrix_differentiableAt χ e x hχ
  have hentry := scalar_array_fderiv_entry (scalarCoordinateMatrix χ e) x
  have htransport : H = DB + M * DV + ∑ i, V i x • T i := by
    apply Matrix.ext
    intro i j
    have hsum : (∑ l, V l x • T l) i j =
        ∑ l, V l x * scalarPartial (fun y => scalarCoordinateMatrix χ e y i j) (e l) x := by
      rw [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro l _
      change V l x * fderiv ℝ (scalarCoordinateMatrix χ e) x (e l) i j = _
      rw [hentry (e l) hMd i j]
    change fderiv ℝ (scalarCoordinateMatrix χ e) x a i j =
      DB i j + (M * DV) i j + (∑ l, V l x • T l) i j
    rw [hentry a hMd i j, Matrix.mul_apply, hsum]
    exact scalarCoordinate_transport_entry χ e a x V hχ hV i j
  have h := determinant_current_matrix_identity M H DB DV (fun i => V i x) T hdet htransport
  have hj (v : E) : scalarPartial (scalarCoordinateDet χ e) v x =
      scalarDeterminantDerivative M (fderiv ℝ (scalarCoordinateMatrix χ e) x v) :=
    scalarDeterminant_real_fderiv_apply (scalarCoordinateMatrix χ e) x v hMd
  rw [hj a]
  simp_rw [hj]
  exact h

omit [DecidableEq ι] in
theorem finite_current_product_algebra (J b Ja ba D : ℂ)
    (V dV dJ db : ι → ℂ)
    (hJ : Ja - (∑ i, V i * dJ i) - J * (∑ i, dV i) = J * D) :
    Ja * b + J * ba - (∑ i, ((dV i * J + V i * dJ i) * b + (V i * J) * db i)) =
      J * (ba - (∑ i, V i * db i) + D * b) := by
  have hs : (∑ i, ((dV i * J + V i * dJ i) * b + (V i * J) * db i)) =
      ((∑ i, dV i) * J + ∑ i, V i * dJ i) * b + J * ∑ i, V i * db i := by
    calc
      _ = ∑ i, ((dV i * J) * b + (V i * dJ i) * b + J * (V i * db i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
  rw [hs]
  linear_combination b * hJ

/-- The exact complex scalar current on the original real angular
coordinates, including parameter-dependent transported amplitudes.
The regular divergence is constructed from χ and V, not supplied as
an additional current hypothesis. -/
theorem exact_scalar_current (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (V : ι → E → ℂ) (b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (hb : DifferentiableAt ℝ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarPartial (fun y => scalarCoordinateDet χ e y * b y) a x -
        (∑ i, scalarPartial (fun y => V i y * scalarCoordinateDet χ e y * b y) (e i) x) =
      scalarCoordinateDet χ e x *
        (scalarPartial b a x - (∑ i, V i x * scalarPartial b (e i) x) +
          scalarTransportDivergence χ e a V x * b x) := by
  have hJ := scalarCoordinateDet_differentiableAt χ e x hχ
  rw [scalarPartial_mul _ _ a x hJ hb]
  have hi (i : ι) : scalarPartial (fun y => V i y * scalarCoordinateDet χ e y * b y) (e i) x =
      (scalarPartial (V i) (e i) x * scalarCoordinateDet χ e x +
        V i x * scalarPartial (scalarCoordinateDet χ e) (e i) x) * b x +
        (V i x * scalarCoordinateDet χ e x) * scalarPartial b (e i) x := by
    rw [scalarPartial_mul (fun y => V i y * scalarCoordinateDet χ e y) b (e i) x
      ((hV i).mul hJ) hb,
      scalarPartial_mul (V i) (scalarCoordinateDet χ e) (e i) x (hV i) hJ]
  simp_rw [hi]
  exact finite_current_product_algebra _ _ _ _ _ _ _ _ _
    (scalarCoordinateDet_current χ e a x V hχ hV hdet)

end IsingBulk.AnisoF002.Isotropic
