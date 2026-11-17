import IsingBulk.AnisoF002.C03.IsotropicAffineConstraintCalculus
import IsingBulk.AnisoF002.C03.IsotropicSmoothTransport
import IsingBulk.AnisoF002.C03.IsotropicSmoothCompactIntegral

/-!
# The actual balanced homotopy current on the affine angular constraint

The full Jacobian and inverse-Jacobian velocity are the derivatives of
the real smooth balanced deformation. The velocity is tangent on an
open neighborhood. The complete current then becomes the ordinary
real divergence in the exact eliminated-angle chart.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix ContDiff
open Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def homotopyPulledDensity (η τ : ℝ) (F : (ι → ℂ) → ℂ) (q : ℝ × (ι → ℝ)) : ℂ :=
  scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection q *
    F (fun i => homotopyCoordinate η τ i q)

def homotopyCurrentFlux (η τ : ℝ) (F : (ι → ℂ) → ℂ) (i : ι)
    (q : ℝ × (ι → ℝ)) : ℂ :=
  actualHomotopyVelocity η τ i q * homotopyPulledDensity η τ F q

theorem homotopyPulledDensity_actual (η τ : ℝ) (F : (ι → ℂ) → ℂ)
    (q : ℝ × (ι → ℝ)) :
    homotopyPulledDensity η τ F q =
      (actualBalancedJacobian η τ q.1 q.2).det *
        F (actualHomotopyAngle η τ q.1 q.2) := by
  rw [homotopyPulledDensity, homotopyCoordinate_determinant]
  rfl

theorem homotopyPulledDensity_contDiffAt (η τ : ℝ) (F : (ι → ℂ) → ℂ)
    (q : ℝ × (ι → ℝ))
    (hF : AnalyticAt ℂ F (actualHomotopyAngle η τ q.1 q.2)) :
    ContDiffAt ℝ ∞ (homotopyPulledDensity η τ F) q := by
  have hχ (i : ι) : ContDiffAt ℝ ∞ (homotopyCoordinate η τ i) q :=
    (homotopyCoordinate_contDiff η τ i ⊤).contDiffAt
  exact (scalarMatrixDet_contDiffAt _ q
    (scalarCoordinateMatrix_contDiffAt _ homotopyAngularDirection q hχ)).mul
      (hF.restrictScalars.contDiffAt.comp q (contDiffAt_pi.mpr hχ))

theorem actualHomotopyVelocity_contDiffAt (η τ : ℝ) (q : ℝ × (ι → ℝ))
    (hdet : (actualBalancedJacobian η τ q.1 q.2).det ≠ 0) (i : ι) :
    ContDiffAt ℝ ∞ (actualHomotopyVelocity η τ i) q := by
  have hχ (j : ι) : ContDiffAt ℝ ∞ (homotopyCoordinate η τ j) q :=
    (homotopyCoordinate_contDiff η τ j ⊤).contDiffAt
  have hd : scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection q ≠ 0 := by
    rwa [homotopyCoordinate_determinant]
  change ContDiffAt ℝ ∞ (fun y => ∑ j,
    scalarInverseEntry (scalarCoordinateMatrix (homotopyCoordinate η τ)
      homotopyAngularDirection y) i j *
      (scalarPartial (homotopyCoordinate η τ j) homotopyTimeDirection y - 0)) q
  apply ContDiffAt.sum
  intro j _
  exact (scalarInverseEntry_contDiffAt _ q
    (scalarCoordinateMatrix_contDiffAt _ homotopyAngularDirection q hχ) hd i j).mul
    ((scalarPartial_contDiffAt _ homotopyTimeDirection q (hχ j)).sub contDiffAt_const)

theorem homotopyCurrentFlux_contDiffAt (η τ : ℝ) (F : (ι → ℂ) → ℂ)
    (q : ℝ × (ι → ℝ))
    (hF : AnalyticAt ℂ F (actualHomotopyAngle η τ q.1 q.2))
    (hdet : (actualBalancedJacobian η τ q.1 q.2).det ≠ 0) (i : ι) :
    ContDiffAt ℝ ∞ (homotopyCurrentFlux η τ F i) q :=
  (actualHomotopyVelocity_contDiffAt η τ q hdet i).mul
    (homotopyPulledDensity_contDiffAt η τ F q hF)

theorem homotopyCurrentFlux_tangent (η τ : ℝ) (F : (ι → ℂ) → ℂ)
    (q : ℝ × (ι → ℝ))
    (hdet : (actualBalancedJacobian η τ q.1 q.2).det ≠ 0) :
    (fun y => ∑ i, homotopyCurrentFlux η τ F i y) =ᶠ[𝓝 q] (fun _ => 0) := by
  have hχ (j : ι) : ContDiffAt ℝ 2 (homotopyCoordinate η τ j) q :=
    (homotopyCoordinate_contDiff η τ j 2).contDiffAt
  have hd : scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection q ≠ 0 := by
    rwa [homotopyCoordinate_determinant]
  filter_upwards [(scalarCoordinateDet_differentiableAt _ homotopyAngularDirection q hχ).continuousAt.eventually_ne hd]
    with y hy
  have hdy : (actualBalancedJacobian η τ y.1 y.2).det ≠ 0 := by
    rwa [homotopyCoordinate_determinant] at hy
  simp only [homotopyCurrentFlux, ← Finset.sum_mul,
    actualHomotopyVelocity_sum_zero η τ y hdy, zero_mul]

theorem actual_homotopy_current_pointwise (η τ : ℝ) (F : (ι → ℂ) → ℂ)
    (q : ℝ × (ι → ℝ))
    (hF : AnalyticAt ℂ F (actualHomotopyAngle η τ q.1 q.2))
    (hdet : (actualBalancedJacobian η τ q.1 q.2).det ≠ 0) :
    deriv (fun u : ℝ => homotopyPulledDensity η τ F (u, q.2)) q.1 =
      ∑ i, scalarPartial (fun θ => homotopyCurrentFlux η τ F i (q.1, θ))
        (Pi.single i 1) q.2 := by
  have hχ (j : ι) : ContDiffAt ℝ 2 (homotopyCoordinate η τ j) q :=
    (homotopyCoordinate_contDiff η τ j 2).contDiffAt
  have hd : scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection q ≠ 0 := by
    rwa [homotopyCoordinate_determinant]
  have hc := exact_holomorphic_pullback_current (homotopyCoordinate η τ)
    homotopyAngularDirection homotopyTimeDirection q F hχ hF.differentiableAt hd
  have he : scalarPartial (homotopyPulledDensity η τ F) homotopyTimeDirection q =
      ∑ i, scalarPartial (homotopyCurrentFlux η τ F i) (homotopyAngularDirection i) q := by
    apply sub_eq_zero.mp
    change scalarPartial (fun y => scalarCoordinateDet (homotopyCoordinate η τ)
        homotopyAngularDirection y * F (fun i => homotopyCoordinate η τ i y))
        homotopyTimeDirection q -
      (∑ i, scalarPartial (fun y => constructedAngularVelocity (homotopyCoordinate η τ)
        homotopyAngularDirection homotopyTimeDirection (fun _ _ => 0) i y *
          (scalarCoordinateDet (homotopyCoordinate η τ) homotopyAngularDirection y *
            F (fun j => homotopyCoordinate η τ j y))) (homotopyAngularDirection i) q) = 0
    simpa only [mul_assoc] using hc
  rw [homotopyTimeDirection, scalarPartial_time_slice _ q
    ((homotopyPulledDensity_contDiffAt η τ F q hF).differentiableAt (by simp))] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarPartial_angular_slice _ q _
    ((homotopyCurrentFlux_contDiffAt η τ F q hF hdet i).differentiableAt (by simp))

/-- Pointwise homotopy conservation in the original N-1 real variables.
No contour-invariance premise and no artificial integration measure. -/
theorem actual_homotopy_affine_current {n : ℕ} (η τ a ξ : ℝ)
    (F : (Fin (n + 1) → ℂ) → ℂ) (x : Fin n → ℝ)
    (hF : AnalyticAt ℂ F (actualHomotopyAngle η τ ξ (affineConstraintAngles a x)))
    (hdet : (actualBalancedJacobian η τ ξ (affineConstraintAngles a x)).det ≠ 0) :
    deriv (fun u : ℝ => homotopyPulledDensity η τ F (u, affineConstraintAngles a x)) ξ =
      ∑ i, scalarPartial (fun y => homotopyCurrentFlux η τ F i.castSucc
        (ξ, affineConstraintAngles a y)) (Pi.single i 1) x := by
  have hD (i : Fin (n + 1)) : DifferentiableAt ℝ
      (fun θ => homotopyCurrentFlux η τ F i (ξ, θ)) (affineConstraintAngles a x) :=
    ((homotopyCurrentFlux_contDiffAt η τ F (ξ, affineConstraintAngles a x) hF hdet i).differentiableAt
      (by simp)).comp _ (differentiableAt_const ξ |>.prodMk differentiableAt_id)
  have ht := homotopyCurrentFlux_tangent η τ F (ξ, affineConstraintAngles a x) hdet
  have hmap : ContinuousAt (fun θ : Fin (n + 1) → ℝ => (ξ, θ)) (affineConstraintAngles a x) :=
    continuousAt_const.prodMk continuousAt_id
  have ht' : (fun θ => ∑ i, homotopyCurrentFlux η τ F i (ξ, θ))
      =ᶠ[𝓝 (affineConstraintAngles a x)] (fun _ => 0) := ht.comp_tendsto hmap
  rw [affineConstraint_tangent_divergence a _ x hD ht']
  exact actual_homotopy_current_pointwise η τ F (ξ, affineConstraintAngles a x) hF hdet

theorem exists_actual_homotopy_invertible (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N → ∀ τ ∈ Icc 0 δ,
      ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ, (actualBalancedJacobian η τ ξ θ).det ≠ 0 := by
  obtain ⟨δ, _, hδ, _, hreg⟩ := exists_actual_balanced_uniform_regularity η
  refine ⟨δ, hδ, ?_⟩
  intro N hN τ hτ ξ hξ θ hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
    (LinearMap.ker_eq_bot.mpr (hreg N hN τ hτ ξ hξ θ).1.1)

end IsingBulk.AnisoF002.Isotropic
