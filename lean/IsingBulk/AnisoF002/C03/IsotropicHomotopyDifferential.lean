import IsingBulk.AnisoF002.C03.IsotropicHolomorphicPullbackCurrent
import IsingBulk.AnisoF002.C03.IsotropicActualCoordinates

/-!
# The full differential of the actual balanced homotopy in its time variable

Both populations vary with every real angular coordinate. The actual
coordinate matrix is exactly the complete balanced Jacobian; the time
velocity is solved from it and has zero total angular component.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualHomotopyDisplacement (η τ : ℝ) (θ : ι → ℝ) (i : ι) : ℝ :=
  balancedShift (τ / Fintype.card ι) (fun j => upperPeriodicBump η (θ j))
    (fun j => lowerPeriodicBump η (θ j)) i

omit [DecidableEq ι] in
theorem actualHomotopyAngle_affine_time (η τ ξ : ℝ) (θ : ι → ℝ) (i : ι) :
    actualHomotopyAngle η τ ξ θ i = (θ i : ℂ) - Complex.I * (ξ : ℂ) * actualHomotopyDisplacement η τ θ i := by
  simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
    balancedShift, actualHomotopyDisplacement, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

def homotopyCoordinate (η τ : ℝ) (i : ι) (q : ℝ × (ι → ℝ)) : ℂ :=
  actualHomotopyAngle η τ q.1 q.2 i

def homotopyAngularDirection (i : ι) : ℝ × (ι → ℝ) := (0, Pi.single i 1)

def homotopyTimeDirection : ℝ × (ι → ℝ) := (1, 0)

omit [DecidableEq ι] in
theorem homotopyCoordinate_contDiff (η τ : ℝ) (i : ι) (n : ℕ∞) :
    ContDiff ℝ n (homotopyCoordinate η τ i) := by
  have hp (j : ι) : ContDiff ℝ n (fun q : ℝ × (ι → ℝ) => upperPeriodicBump η (q.2 j)) :=
    (upperPeriodicBump_contDiff η).comp ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
  have hm (j : ι) : ContDiff ℝ n (fun q : ℝ × (ι → ℝ) => lowerPeriodicBump η (q.2 j)) :=
    (lowerPeriodicBump_contDiff η).comp ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
  have hD : ContDiff ℝ n (fun q : ℝ × (ι → ℝ) => actualHomotopyDisplacement η τ q.2 i) :=
    contDiff_const.mul (((ContDiff.sum (fun j _ => hp j)).mul (hm i)).sub
      ((ContDiff.sum (fun j _ => hm j)).mul (hp i)))
  have he : homotopyCoordinate η τ i = fun q : ℝ × (ι → ℝ) =>
      (q.2 i : ℂ) - Complex.I * (q.1 : ℂ) * actualHomotopyDisplacement η τ q.2 i :=
    funext (fun q => actualHomotopyAngle_affine_time η τ q.1 q.2 i)
  rw [he]
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd)).sub
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).mul
      (Complex.ofRealCLM.contDiff.comp hD))

theorem scalarPartial_time_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → ℂ) (q : ℝ × E) (hf : DifferentiableAt ℝ f q) :
    scalarPartial f (1, 0) q = deriv (fun u : ℝ => f (u, q.2)) q.1 := by
  have hline : HasDerivAt (fun u : ℝ => (u, q.2)) (1, 0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt q.1 hline).deriv.symm

theorem scalarPartial_angular_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → ℂ) (q : ℝ × E) (v : E) (hf : DifferentiableAt ℝ f q) :
    scalarPartial f (0, v) q = fderiv ℝ (fun y : E => f (q.1, y)) q.2 v := by
  have hi : HasFDerivAt (fun y : E => (q.1, y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hd := hf.hasFDerivAt.comp q.2 hi
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl

omit [DecidableEq ι] in
theorem homotopyCoordinate_timePartial (η τ : ℝ) (q : ℝ × (ι → ℝ)) (i : ι) :
    scalarPartial (homotopyCoordinate η τ i) homotopyTimeDirection q =
      -Complex.I * actualHomotopyDisplacement η τ q.2 i := by
  rw [show homotopyTimeDirection = (1, (0 : ι → ℝ)) from rfl,
    scalarPartial_time_slice _ q ((homotopyCoordinate_contDiff η τ i 1).differentiable_one q)]
  have he : (fun u : ℝ => homotopyCoordinate η τ i (u, q.2)) =
      fun u : ℝ => (q.2 i : ℂ) - Complex.I * (u : ℂ) * actualHomotopyDisplacement η τ q.2 i :=
    funext (fun u => actualHomotopyAngle_affine_time η τ u q.2 i)
  rw [he]
  have hd := (hasDerivAt_const q.1 (q.2 i : ℂ)).sub
    ((Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).mul_const
      (actualHomotopyDisplacement η τ q.2 i : ℂ))
  simpa only [Pi.sub_def, Complex.ofRealCLM_apply, Complex.ofReal_one, zero_sub, mul_one, neg_mul] using hd.deriv

omit [DecidableEq ι] in
theorem homotopyCoordinate_timePartial_sum (η τ : ℝ) (q : ℝ × (ι → ℝ)) :
    ∑ i, scalarPartial (homotopyCoordinate η τ i) homotopyTimeDirection q = 0 := by
  simp_rw [homotopyCoordinate_timePartial]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]
  have hh : ∑ i, actualHomotopyDisplacement η τ q.2 i = 0 := sum_balancedShift _ _ _
  rw [hh, Complex.ofReal_zero, mul_zero]

theorem homotopyCoordinate_matrix (η τ : ℝ) (q : ℝ × (ι → ℝ)) :
    scalarCoordinateMatrix (homotopyCoordinate η τ) homotopyAngularDirection q =
      actualBalancedMatrix η τ q.1 q.2 := by
  apply Matrix.ext
  intro i j
  change scalarPartial (homotopyCoordinate η τ i) (0, Pi.single j 1) q = _
  rw [scalarPartial_angular_slice _ q _
    ((homotopyCoordinate_contDiff η τ i 1).differentiable_one q)]
  change fderiv ℝ (fun θ : ι → ℝ => actualHomotopyAngle η τ q.1 θ i) q.2 (Pi.single j 1) = _
  rw [actualHomotopyAngle_fderiv]
  have he : (fun k => (((Pi.single j (1 : ℝ) : ι → ℝ) k) : ℂ)) =
      (Pi.single j (1 : ℂ) : ι → ℂ) := by
    funext k
    by_cases h : j = k
    · subst k
      simp
    · simp [h]
  rw [he]
  rfl

theorem homotopyCoordinate_determinant (η τ : ℝ) (q : ℝ × (ι → ℝ)) :
    scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection q =
      (actualBalancedJacobian η τ q.1 q.2).det := by
  rw [scalarCoordinateDet, homotopyCoordinate_matrix, actualBalancedMatrix, LinearMap.det_toMatrix']

theorem actualBalancedMatrix_column_sum (η τ ξ : ℝ) (θ : ι → ℝ) (j : ι) :
    ∑ i, actualBalancedMatrix η τ ξ θ i j = 1 := by
  have hh := sum_balancedAngularJacobian ((ξ * τ) / Fintype.card ι)
    (fun i => upperPeriodicBump η (θ i)) (fun i => lowerPeriodicBump η (θ i))
    (fun i => deriv (upperPeriodicBump η) (θ i))
    (fun i => deriv (lowerPeriodicBump η) (θ i)) (Pi.single j (1 : ℂ))
  simpa [actualBalancedMatrix, LinearMap.toMatrix'_apply, actualBalancedJacobian] using hh

def actualHomotopyVelocity (η τ : ℝ) (i : ι) (q : ℝ × (ι → ℝ)) : ℂ :=
  constructedAngularVelocity (homotopyCoordinate η τ) homotopyAngularDirection
    homotopyTimeDirection (fun _ _ => 0) i q

theorem actualHomotopyVelocity_sum_zero (η τ : ℝ) (q : ℝ × (ι → ℝ))
    (hdet : (actualBalancedJacobian η τ q.1 q.2).det ≠ 0) :
    ∑ i, actualHomotopyVelocity η τ i q = 0 := by
  have hh := matrix_inverse_velocity_zero_sum (actualBalancedMatrix η τ q.1 q.2)
    (fun i => scalarPartial (homotopyCoordinate η τ i) homotopyTimeDirection q)
    (by rwa [actualBalancedMatrix, LinearMap.det_toMatrix'])
    (actualBalancedMatrix_column_sum η τ q.1 q.2) (homotopyCoordinate_timePartial_sum η τ q)
  simpa only [actualHomotopyVelocity, constructedAngularVelocity, sub_zero,
    homotopyCoordinate_matrix, scalarInverseAction] using hh

end IsingBulk.AnisoF002.Isotropic
