import IsingBulk.AnisoF002.C03.IsotropicActualCovariance
import IsingBulk.AnisoF002.C03.IsotropicScalarCurrentIdentity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The actual regular coordinates as smooth functions of real angles

These derivatives belong to the actual upper-half-plane physical sheet.
The full balanced deformation is differentiated before the regular
coordinate is introduced; both population derivatives are retained.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric

theorem upperPhysicalPhase_sin_ne_zero (W : ℂ) (hW : 0 < W.im) :
    Complex.sin (upperPhysicalPhase W) ≠ 0 := by
  have h := upperPhysicalPhase_pair_sine_ne_zero W W hW hW
  simpa only [add_self_div_two] using h

theorem upperPhysicalPhase_hasDerivAt (W : ℂ) (hW : 0 < W.im) :
    HasDerivAt upperPhysicalPhase (-1 / Complex.sin (upperPhysicalPhase W)) W := by
  have hd := (upperPhysicalPhase_analyticAt W hW).differentiableAt.hasDerivAt
  have hc := hd.ccos
  have he : (fun z => Complex.cos (upperPhysicalPhase z)) = id := funext upperPhysicalPhase_cos
  rw [he] at hc
  have hu := hc.unique (hasDerivAt_id W)
  have hs := upperPhysicalPhase_sin_ne_zero W hW
  apply hd.congr_deriv
  apply (eq_div_iff hs).mpr
  linear_combination -hu

theorem physicalRegularCoordinate_analyticAt (q : ℂ × ℂ)
    (hq : 0 < (isotropicDispersion q).im) : AnalyticAt ℂ physicalRegularCoordinate q := by
  exact analyticAt_snd.add ((upperPhysicalPhase_analyticAt _ hq).comp
    (f := isotropicDispersion) (analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd)))

def physicalCoordinateDifferential (q : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.snd ℂ ℂ ℂ +
    (-1 / Complex.sin (upperPhysicalPhase (isotropicDispersion q))) •
      (ContinuousLinearMap.fst ℂ ℂ ℂ -
        (-Complex.sin q.2) • ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem physicalRegularCoordinate_hasFDerivAt (q : ℂ × ℂ)
    (hq : 0 < (isotropicDispersion q).im) :
    HasFDerivAt physicalRegularCoordinate (physicalCoordinateDifferential q) q := by
  have hd := (hasFDerivAt_fst (𝕜 := ℂ) (p := q)).sub
    ((Complex.hasDerivAt_cos q.2).comp_hasFDerivAt q (hasFDerivAt_snd (𝕜 := ℂ) (p := q)))
  exact (hasFDerivAt_snd (𝕜 := ℂ) (p := q)).add
    ((upperPhysicalPhase_hasDerivAt _ hq).comp_hasFDerivAt q hd)

theorem physicalCoordinateDifferential_apply (q h : ℂ × ℂ) :
    physicalCoordinateDifferential q h =
      (1 - Complex.sin q.2 / Complex.sin (upperPhysicalPhase (isotropicDispersion q))) * h.2 -
        h.1 / Complex.sin (upperPhysicalPhase (isotropicDispersion q)) := by
  change h.2 + (-1 / Complex.sin (upperPhysicalPhase (isotropicDispersion q))) *
    (h.1 - (-Complex.sin q.2) * h.2) = _
  ring

variable {ι : Type*} [Fintype ι]

theorem actualHomotopyAngle_contDiff (η τ ξ : ℝ) (i : ι) (n : ℕ∞) :
    ContDiff ℝ n (fun θ : ι → ℝ => actualHomotopyAngle η τ ξ θ i) := by
  have hp (j : ι) : ContDiff ℝ n (fun θ : ι → ℝ => upperPeriodicBump η (θ j)) :=
    (upperPeriodicBump_contDiff η).comp (contDiff_apply ℝ ℝ j)
  have hm (j : ι) : ContDiff ℝ n (fun θ : ι → ℝ => lowerPeriodicBump η (θ j)) :=
    (lowerPeriodicBump_contDiff η).comp (contDiff_apply ℝ ℝ j)
  have hs : ContDiff ℝ n (fun θ : ι → ℝ => balancedShift (ξ * (τ / Fintype.card ι))
      (fun j => upperPeriodicBump η (θ j)) (fun j => lowerPeriodicBump η (θ j)) i) := by
    exact contDiff_const.mul (((ContDiff.sum (fun j _ => hp j)).mul (hm i)).sub
      ((ContDiff.sum (fun j _ => hm j)).mul (hp i)))
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hs))

theorem actualHomotopyAngle_fderiv (η τ ξ : ℝ) (θ a : ι → ℝ) (i : ι) :
    fderiv ℝ (fun y : ι → ℝ => actualHomotopyAngle η τ ξ y i) θ a =
      actualBalancedJacobian η τ ξ θ (fun j => (a j : ℂ)) i := by
  have hp : HasDerivAt (fun t : ℝ => θ + t • a) a 0 := by
    simpa only [one_smul, id_eq, zero_add] using!
      (hasDerivAt_const (0 : ℝ) θ).add ((hasDerivAt_id (0 : ℝ)).smul_const a)
  have hd := ((actualHomotopyAngle_contDiff η τ ξ i 1).differentiable_one θ).hasFDerivAt
  have hd' : HasFDerivAt (fun y : ι → ℝ => actualHomotopyAngle η τ ξ y i)
      (fderiv ℝ (fun y : ι → ℝ => actualHomotopyAngle η τ ξ y i) θ) (θ + (0 : ℝ) • a) := by
    simpa only [zero_smul, add_zero] using hd
  have hc := hd'.comp_hasDerivAt 0 hp
  have hθ (j : ι) : HasDerivAt (fun t : ℝ => θ j + t * a j) (a j) 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const (a j)).const_add (θ j)
  have hb := balancedContourPath_derivative_jacobian
    ((ξ * τ) / Fintype.card ι) 0 (fun j t => θ j + t * a j)
    (upperPeriodicBump η) (lowerPeriodicBump η) a
    (fun j => deriv (upperPeriodicBump η) (θ j))
    (fun j => deriv (lowerPeriodicBump η) (θ j)) hθ
    (fun j => by simpa only [zero_mul, add_zero] using
      ((upperPeriodicBump_contDiff η : ContDiff ℝ 1 _).differentiable_one (θ j)).hasDerivAt)
    (fun j => by simpa only [zero_mul, add_zero] using
      ((lowerPeriodicBump_contDiff η : ContDiff ℝ 1 _).differentiable_one (θ j)).hasDerivAt) i
  have hscale : ξ * (τ / (Fintype.card ι : ℝ)) = (ξ * τ) / Fintype.card ι := by ring
  have hc' : HasDerivAt
      (fun t : ℝ => actualHomotopyAngle η τ ξ (θ + t • a) i)
      (actualBalancedJacobian η τ ξ θ (fun j => (a j : ℂ)) i) 0 := by
    simpa only [actualHomotopyAngle, balancedHomotopyCoordinate, balancedContourPath,
      actualBalancedJacobian, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      zero_mul, add_zero, hscale, contourCoordinate] using hb
  exact hc.unique hc'

def actualPhysicalCoordinate (η τ ξ : ℝ) (i : ι) (q : ℂ × (ι → ℝ)) : ℂ :=
  physicalRegularCoordinate (q.1, actualHomotopyAngle η τ ξ q.2 i)

theorem actualPhysicalCoordinate_contDiffAt (η τ ξ : ℝ) (i : ι)
    (q : ℂ × (ι → ℝ)) (n : ℕ∞)
    (hq : 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im) :
    ContDiffAt ℝ n (actualPhysicalCoordinate η τ ξ i) q := by
  have hχ : ContDiffAt ℝ n physicalRegularCoordinate
      (q.1, actualHomotopyAngle η τ ξ q.2 i) :=
    (physicalRegularCoordinate_analyticAt _ hq).restrictScalars.contDiffAt
  exact hχ.comp q (contDiffAt_fst.prodMk
    ((actualHomotopyAngle_contDiff η τ ξ i n).contDiffAt.comp q contDiffAt_snd))

theorem actualPhysicalCoordinate_fderiv (η τ ξ : ℝ) (i : ι)
    (q h : ℂ × (ι → ℝ))
    (hq : 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im) :
    fderiv ℝ (actualPhysicalCoordinate η τ ξ i) q h =
      (1 - Complex.sin (actualHomotopyAngle η τ ξ q.2 i) /
        Complex.sin (upperPhysicalPhase (isotropicDispersion
          (q.1, actualHomotopyAngle η τ ξ q.2 i)))) *
        actualBalancedJacobian η τ ξ q.2 (fun j => (h.2 j : ℂ)) i -
      h.1 / Complex.sin (upperPhysicalPhase (isotropicDispersion
        (q.1, actualHomotopyAngle η τ ξ q.2 i))) := by
  have hw := ((actualHomotopyAngle_contDiff η τ ξ i 1).differentiable_one q.2).hasFDerivAt
  have hmap := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).prodMk
    (hw.comp q (hasFDerivAt_snd (p := q)))
  have hc := ((physicalRegularCoordinate_hasFDerivAt _ hq).restrictScalars ℝ).comp q hmap
  change HasFDerivAt (actualPhysicalCoordinate η τ ξ i) _ q at hc
  rw [hc.fderiv]
  change physicalCoordinateDifferential
      (q.1, actualHomotopyAngle η τ ξ q.2 i)
      (h.1, fderiv ℝ (fun y : ι → ℝ => actualHomotopyAngle η τ ξ y i) q.2 h.2) = _
  rw [physicalCoordinateDifferential_apply, actualHomotopyAngle_fderiv]

end IsingBulk.AnisoF002.Isotropic
