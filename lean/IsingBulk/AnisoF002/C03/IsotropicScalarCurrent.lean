import IsingBulk.AnisoF002.C03.IsotropicScalarJacobi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The complex scalar current in real angular coordinates

Real directional derivatives act on complex scalar coefficients. The
Jacobian is the determinant of the full complex coordinate matrix.
The transport velocity is defined from the actual coordinate map;
mixed derivatives and Jacobi differentiation give the scalar current.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarPartial (f : E → ℂ) (v : E) (x : E) : ℂ := fderiv ℝ f x v

theorem scalarPartial_mul (f g : E → ℂ) (v x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarPartial (fun y => f y * g y) v x =
      scalarPartial f v x * g x + f x * scalarPartial g v x := by
  simp only [scalarPartial, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

theorem scalarPartial_sub (f g : E → ℂ) (v x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarPartial (fun y => f y - g y) v x = scalarPartial f v x - scalarPartial g v x := by
  simp only [scalarPartial, fderiv_fun_sub hf hg, sub_apply]

theorem scalarPartial_sum {ι : Type*} [Fintype ι] (f : ι → E → ℂ) (v x : E)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    scalarPartial (fun y => ∑ i, f i y) v x = ∑ i, scalarPartial (f i) v x := by
  simp only [scalarPartial, fderiv_fun_sum (fun i _ => hf i), sum_apply]

theorem scalarPartial_differentiableAt (f : E → ℂ) (v x : E)
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (scalarPartial f v) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hd.clm_apply (differentiableAt_const v)

theorem scalarPartial_second (f : E → ℂ) (u v x : E) (hf : ContDiffAt ℝ 2 f x) :
    scalarPartial (scalarPartial f u) v x = fderiv ℝ (fderiv ℝ f) x v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change fderiv ℝ (fun y => (fderiv ℝ f y) u) x v = _
  simp only [fderiv_clm_apply hd (differentiableAt_const u),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

theorem scalarPartial_comm (f : E → ℂ) (u v x : E) (hf : ContDiffAt ℝ 2 f x) :
    scalarPartial (scalarPartial f u) v x = scalarPartial (scalarPartial f v) u x := by
  rw [scalarPartial_second f u v x hf, scalarPartial_second f v u x hf]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq v u

variable {ι : Type*} [Fintype ι]

def scalarCoordinateMatrix (χ : ι → E → ℂ) (e : ι → E) (x : E) : ι → ι → ℂ :=
  fun i j => scalarPartial (χ i) (e j) x

def scalarTransportVelocity (χ : ι → E → ℂ) (e : ι → E) (a : E)
    (V : ι → E → ℂ) (x : E) (i : ι) : ℂ :=
  scalarPartial (χ i) a x - ∑ j, scalarCoordinateMatrix χ e x i j * V j x

theorem scalarCoordinateMatrix_differentiableAt (χ : ι → E → ℂ) (e : ι → E) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x) :
    DifferentiableAt ℝ (scalarCoordinateMatrix χ e) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  exact scalarPartial_differentiableAt (χ i) (e j) x (hχ i)

theorem scalarTransportVelocity_differentiableAt (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (V : ι → E → ℂ) (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (i : ι) :
    DifferentiableAt ℝ (fun y => scalarTransportVelocity χ e a V y i) x := by
  apply (scalarPartial_differentiableAt (χ i) a x (hχ i)).sub
  apply DifferentiableAt.fun_sum
  intro j _
  exact (scalarPartial_differentiableAt (χ i) (e j) x (hχ i)).mul (hV j)

/-- Differentiating the actual defining velocity gives the full matrix
transport relation. The two mixed derivatives commute because χ is C². -/
theorem scalarCoordinate_transport_entry (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (V : ι → E → ℂ) (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (i j : ι) :
    scalarPartial (fun y => scalarCoordinateMatrix χ e y i j) a x =
      scalarPartial (fun y => scalarTransportVelocity χ e a V y i) (e j) x +
        (∑ l, scalarCoordinateMatrix χ e x i l * scalarPartial (V l) (e j) x) +
        ∑ l, V l x * scalarPartial (fun y => scalarCoordinateMatrix χ e y i j) (e l) x := by
  have hd := fun l => scalarPartial_differentiableAt (χ i) (e l) x (hχ i)
  have hsum : DifferentiableAt ℝ
      (fun y => ∑ l, scalarCoordinateMatrix χ e y i l * V l y) x := by
    exact DifferentiableAt.fun_sum (fun l _ => (hd l).mul (hV l))
  dsimp only [scalarCoordinateMatrix, scalarTransportVelocity] at *
  rw [scalarPartial_sub _ _ (e j) x (scalarPartial_differentiableAt (χ i) a x (hχ i)) hsum,
    scalarPartial_sum (fun l y => scalarPartial (χ i) (e l) y * V l y)
      (e j) x (fun l => (hd l).mul (hV l))]
  simp_rw [scalarPartial_mul _ _ (e j) x (hd _) (hV _), Finset.sum_add_distrib]
  have htime : scalarPartial (scalarPartial (χ i) a) (e j) x =
      scalarPartial (scalarPartial (χ i) (e j)) a x := scalarPartial_comm (χ i) a (e j) x (hχ i)
  rw [htime]
  have hcross : (∑ l, scalarPartial (scalarPartial (χ i) (e l)) (e j) x * V l x) =
      ∑ l, V l x * scalarPartial (scalarPartial (χ i) (e j)) (e l) x := by
    apply Finset.sum_congr rfl
    intro l _
    rw [scalarPartial_comm (χ i) (e l) (e j) x (hχ i)]
    ring
  rw [hcross]
  change scalarPartial (scalarPartial (χ i) (e j)) a x = _
  ring

variable [DecidableEq ι]

theorem scalarDeterminantDerivative_add (M H K : Matrix ι ι ℂ) :
    scalarDeterminantDerivative M (H + K) =
      scalarDeterminantDerivative M H + scalarDeterminantDerivative M K := by
  unfold scalarDeterminantDerivative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : (H + K) i = H i + K i := rfl
  rw [hrow, Matrix.det_updateRow_add]

theorem scalarDeterminantDerivative_smul (M H : Matrix ι ι ℂ) (c : ℂ) :
    scalarDeterminantDerivative M (c • H) = c * scalarDeterminantDerivative M H := by
  unfold scalarDeterminantDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : (c • H) i = c • H i := rfl
  rw [hrow, Matrix.det_updateRow_smul]

theorem scalarDeterminantDerivative_sum (M : Matrix ι ι ℂ) (H : ι → Matrix ι ι ℂ) :
    scalarDeterminantDerivative M (∑ l, H l) = ∑ l, scalarDeterminantDerivative M (H l) := by
  classical
  unfold scalarDeterminantDerivative
  have hlin : ∀ i, (M.updateRow i (∑ l, H l i)).det = ∑ l, (M.updateRow i (H l i)).det := by
    intro i
    exact map_sum (Matrix.detRowAlternating.toMultilinearMap.toLinearMap M i)
      (fun l => H l i) Finset.univ
  calc
    (∑ i, (M.updateRow i ((∑ l, H l) i)).det) =
        ∑ i, ∑ l, (M.updateRow i (H l i)).det := by
      apply Finset.sum_congr rfl
      intro i _
      have hrow : (∑ l, H l) i = ∑ l, H l i := by
        ext j
        simp only [Matrix.sum_apply, Finset.sum_apply]
      rw [hrow, hlin]
    _ = _ := Finset.sum_comm

end IsingBulk.AnisoF002.Isotropic
