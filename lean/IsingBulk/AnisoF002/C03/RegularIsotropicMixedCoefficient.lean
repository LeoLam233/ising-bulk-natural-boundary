import IsingBulk.AnisoF002.C03.RegularIsotropicProtectedDensity
import IsingBulk.AnisoF002.C03.IsotropicJointPhysicalAnalytic
import IsingBulk.AnisoF002.C03.RegularCompactIntegral

/-!
# The actual mixed population coefficient and differentiation under its integral

This is the mixed term of the exact population partition after the full
balanced homotopy. The complete Jacobian and the original N! and angular
normalizations are part of the stored coefficient definition.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail.C03

def mixedAngularAmplitude {N : ℕ} (η τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  (mixedPopulationCutoff η θ : ℂ) * (actualBalancedJacobian η τ 1 θ).det

def mixedPhysicalIntegrand {N : ℕ} (η τ : ℝ) (σ S : ℂ) (θ : Fin N → ℝ) : ℂ :=
  mixedAngularAmplitude η τ θ * isotropicBarePhysicalDensity S σ (actualHomotopyAngle η τ 1 θ)

def mixedPhysicalCoefficient (n : ℕ) (η τ a : ℝ) (σ S : ℂ) : ℂ :=
  ∫ x in angularIntegrationBox n, mixedPhysicalIntegrand η τ σ S (affineConstraintAngles a x)

theorem actualBalancedJacobian_det_continuous {N : ℕ} (η τ ξ : ℝ) :
    Continuous (fun θ : Fin N → ℝ => (actualBalancedJacobian η τ ξ θ).det) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hh := (homotopyPulledDensity_contDiffAt η τ (fun _ : (Fin N → ℂ) => (1 : ℂ))
    (ξ, θ) analyticAt_const).continuousAt.comp
      (f := fun y : Fin N → ℝ => (ξ, y)) (continuousAt_const.prodMk continuousAt_id)
  simpa only [Function.comp_def, homotopyPulledDensity_actual, mul_one] using hh

theorem mixedPopulationCutoff_continuous {N : ℕ} (η : ℝ) :
    Continuous (mixedPopulationCutoff (N := N) η) := by
  have hp : Continuous (actualUpperPopulation (N := N) η) :=
    continuous_finsetSum _ (fun i _ => (upperPeriodicBump_contDiff η (n := 0)).continuous.comp (continuous_apply i))
  have hm : Continuous (actualLowerPopulation (N := N) η) :=
    continuous_finsetSum _ (fun i _ => (lowerPeriodicBump_contDiff η (n := 0)).continuous.comp (continuous_apply i))
  exact ((populationTransition_contDiff (j := 0)).continuous.comp hp).mul
    ((populationTransition_contDiff (j := 0)).continuous.comp hm)

theorem mixedAngularAmplitude_continuous {N : ℕ} (η τ : ℝ) :
    Continuous (mixedAngularAmplitude (N := N) η τ) :=
  (Complex.continuous_ofReal.comp (mixedPopulationCutoff_continuous η)).mul
    (actualBalancedJacobian_det_continuous η τ 1)

theorem actualHomotopyAngles_continuous {N : ℕ} (η τ ξ : ℝ) :
    Continuous (actualHomotopyAngle (ι := Fin N) η τ ξ) :=
  continuous_pi (fun i => (actualHomotopyAngle_contDiff η τ ξ i 0).continuous)

def mixedPhysicalAnalyticFamily {N : ℕ} (σ : ℂ) (p : ℂ × (ℂ × (Fin N → ℂ))) : ℂ :=
  p.2.1 * isotropicBarePhysicalDensity p.1 σ p.2.2

theorem mixedPhysicalAnalyticFamily_analyticAt {N : ℕ} (hN : 0 < N) {σ : ℂ} (hσ : ‖σ‖ ≤ 1)
    (p : ℂ × (ℂ × (Fin N → ℂ)))
    (hp : ∀ i, 0 < (isotropicDispersion (p.1, p.2.2 i)).im) :
    AnalyticAt ℂ (mixedPhysicalAnalyticFamily (N := N) σ) p := by
  have ha : AnalyticAt ℂ (fun q : ℂ × (ℂ × (Fin N → ℂ)) => q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hb : AnalyticAt ℂ (fun q : ℂ × (ℂ × (Fin N → ℂ)) =>
      isotropicBarePhysicalDensity q.1 σ q.2.2) p := by
    apply isotropicBarePhysicalDensity_analytic_parameter hN σ hσ
      (S := fun q : ℂ × (ℂ × (Fin N → ℂ)) => q.1)
      (w := fun q : ℂ × (ℂ × (Fin N → ℂ)) => q.2.2) analyticAt_fst _ hp
    intro i
    exact ((show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _).comp
      (analyticAt_snd.comp analyticAt_snd)
  exact ha.mul hb

theorem mixedPhysicalIntegrand_jets_continuous {N : ℕ} (hN : 0 < N)
    {S σ : ℂ} (hS : 0 < S.im) (hσ : ‖σ‖ ≤ 1)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 ≤ τ) (j : ℕ) :
    Continuous (fun θ : Fin N → ℝ => iteratedDeriv j (fun T => mixedPhysicalIntegrand η τ σ T θ) S) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  let g : (Fin N → ℝ) → ℂ × (Fin N → ℂ) :=
    fun x => (mixedAngularAmplitude η τ x, actualHomotopyAngle η τ 1 x)
  have hg : Continuous g := (mixedAngularAmplitude_continuous η τ).prodMk
    (actualHomotopyAngles_continuous η τ 1)
  have ha := parameterIteratedDeriv_analyticAt
    (mixedPhysicalAnalyticFamily_analyticAt hN hσ (S, g θ)
      (fun i => actual_balanced_homotopy_sheet S hS η τ 1 hη hτ zero_le_one θ i)) j
  exact ha.continuousAt.comp_of_eq (f := fun x => (S, g x))
    (continuousAt_const.prodMk hg.continuousAt) rfl

theorem mixedPhysicalCoefficient_iteratedDeriv (n : ℕ) {η τ : ℝ}
    (hη : 0 < η) (hτ : 0 ≤ τ) (a : ℝ) {S σ : ℂ} (hS : 0 < S.im)
    (hσ : ‖σ‖ ≤ 1) (j : ℕ) :
    iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ) S =
      ∫ x in angularIntegrationBox n,
        iteratedDeriv j (fun T => mixedPhysicalIntegrand η τ σ T (affineConstraintAngles a x)) S := by
  let K := angularIntegrationBox n
  let g : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) :=
    fun x => (mixedAngularAmplitude η τ (affineConstraintAngles a x),
      actualHomotopyAngle η τ 1 (affineConstraintAngles a x))
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hg : Continuous g := ((mixedAngularAmplitude_continuous η τ).prodMk
    (actualHomotopyAngles_continuous η τ 1)).comp ((affineConstraintAngles_contDiff a 0).continuous)
  apply iteratedDeriv_integral_of_joint_analytic (f := mixedPhysicalAnalyticFamily σ) (g := g)
    hK (ae_restrict_mem measurableSet_Icc) hg
  intro x _
  exact mixedPhysicalAnalyticFamily_analyticAt (by omega) hσ (S, g x)
    (fun i => actual_balanced_homotopy_sheet S hS η τ 1 hη hτ zero_le_one (affineConstraintAngles a x) i)

theorem mixedPhysicalCoefficient_jets_integrable (n : ℕ) {η τ : ℝ}
    (hη : 0 < η) (hτ : 0 ≤ τ) (a : ℝ) {S σ : ℂ} (hS : 0 < S.im)
    (hσ : ‖σ‖ ≤ 1) (j : ℕ) :
    IntegrableOn (fun x : Fin n → ℝ =>
      iteratedDeriv j (fun T => mixedPhysicalIntegrand η τ σ T (affineConstraintAngles a x)) S)
      (angularIntegrationBox n) volume :=
  ((mixedPhysicalIntegrand_jets_continuous (by omega) hS hσ hη hτ j).comp
    ((affineConstraintAngles_contDiff a 0).continuous)).continuousOn.integrableOn_compact isCompact_Icc

end
end IsingBulk.AnisoF002.Isotropic
