import IsingBulk.AnisoF002.C03.IsotropicIntegratedHomotopy
import IsingBulk.AnisoF002.C03.IsotropicInitialAmplitude

/-!
# The complete physical isotropic particle density under the actual homotopy

The original normalization, full signed product kernel, every one-body
factor and every canceled physical pair are retained. Its analyticity
on the entire actual deformed image is proved from the physical small
root; its angular periodicity is exact. Thus the preceding integrated
current applies to this complete physical density without added
analytic premises.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter MeasureTheory
open IsingBulk.AnisoF002.RegularTail

def isotropicBarePhysicalDensity {N : ℕ} (s σ : ℂ) (w : Fin N → ℂ) : ℂ :=
  isotropicParticleNormalization N *
    ((1 + σ * ∏ i, isotropicInteriorRoot (s, w i)) /
      (1 - σ * ∏ i, isotropicInteriorRoot (s, w i))) *
    (∏ i, (Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (s, w i))))⁻¹) *
    ∏ ij ∈ indexPairs N, canceledPair 1
      (isotropicInteriorRoot (s, w ij.1)) (isotropicInteriorRoot (s, w ij.2))
      (Complex.exp (w ij.1 * Complex.I)) (Complex.exp (w ij.2 * Complex.I))

theorem physical_product_denominator_of_upper {N : ℕ} (hN : 0 < N) (s σ : ℂ)
    (hσ : ‖σ‖ ≤ 1) (w : Fin N → ℂ)
    (hw : ∀ i, 0 < (isotropicDispersion (s, w i)).im) :
    1 - σ * ∏ i, isotropicInteriorRoot (s, w i) ≠ 0 := by
  have hprod : ‖∏ i, isotropicInteriorRoot (s, w i)‖ < 1 := by
    rw [norm_prod]
    have h := Finset.prod_lt_prod₀ (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => ‖isotropicInteriorRoot (s, w i)‖) (g := fun _ => (1 : ℝ))
      (fun i _ => norm_pos_iff.mpr (isotropicInteriorRoot_ne_zero _))
      (fun i _ => (upperEdgeRoot_norm_lt_one (hw i)).le)
      ⟨⟨0, hN⟩, Finset.mem_univ _, upperEdgeRoot_norm_lt_one (hw ⟨0, hN⟩)⟩
    simpa using h
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul] at he
  have hb := mul_le_mul_of_nonneg_right hσ
    (norm_nonneg (∏ i, isotropicInteriorRoot (s, w i)))
  linarith

theorem isotropicBarePhysicalDensity_analyticAt {N : ℕ} (hN : 0 < N) (s σ : ℂ)
    (hσ : ‖σ‖ ≤ 1) (w : Fin N → ℂ)
    (hw : ∀ i, 0 < (isotropicDispersion (s, w i)).im) :
    AnalyticAt ℂ (isotropicBarePhysicalDensity s σ) w := by
  have hv (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => v i) w :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt w
  have hr (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => isotropicInteriorRoot (s, v i)) w :=
    (isotropicInteriorRoot_analyticAt _ (hw i)).comp
      (f := fun v : Fin N → ℂ => (s, v i)) (analyticAt_const.prod (hv i))
  have hz (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => Complex.exp (v i * Complex.I)) w :=
    ((hv i).mul analyticAt_const).cexp'
  have hphase (i : Fin N) : AnalyticAt ℂ
      (fun v : Fin N → ℂ => upperPhysicalPhase (isotropicDispersion (s, v i))) w :=
    (upperPhysicalPhase_analyticAt _ (hw i)).comp
      (f := fun v : Fin N → ℂ => isotropicDispersion (s, v i))
      (analyticAt_const.sub (Complex.analyticAt_cos.comp (hv i)))
  have hbody (i : Fin N) : AnalyticAt ℂ
      (fun v : Fin N → ℂ => (Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (s, v i))))⁻¹) w := by
    apply (Complex.analyticAt_sinh.comp (analyticAt_const.mul (hphase i))).inv
    change Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (s, w i))) ≠ 0
    rw [mul_comm Complex.I, Complex.sinh_mul_I]
    exact mul_ne_zero (upperPhysicalPhase_sin_ne_zero _ (hw i)) Complex.I_ne_zero
  have hpair (i j : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => canceledPair 1
      (isotropicInteriorRoot (s, v i)) (isotropicInteriorRoot (s, v j))
      (Complex.exp (v i * Complex.I)) (Complex.exp (v j * Complex.I))) w := by
    unfold canceledPair
    apply (((analyticAt_const.mul (((hz i).sub (hz j)).pow 2)).mul (hr i)).mul (hr j)).div
      (((hz i).mul (hz j)).mul ((analyticAt_const.sub ((hr i).mul (hr j))).pow 2))
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      (pow_ne_zero _ (pair_root_denominator_ne_zero
        (upperEdgeRoot_norm_lt_one (hw i)) (upperEdgeRoot_norm_lt_one (hw j))))
  have hprod : AnalyticAt ℂ (fun v : Fin N → ℂ => ∏ i, isotropicInteriorRoot (s, v i)) w :=
    Finset.analyticAt_fun_prod _ (fun i _ => hr i)
  unfold isotropicBarePhysicalDensity
  exact ((analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul hprod)).div
      (analyticAt_const.sub (analyticAt_const.mul hprod))
      (physical_product_denominator_of_upper hN s σ hσ w hw))).mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hbody i))).mul
        (Finset.analyticAt_fun_prod _ (fun ij _ => hpair ij.1 ij.2))

theorem isotropicBarePhysicalDensity_periodic {N : ℕ} (s σ : ℂ) :
    AngularPeriodic (isotropicBarePhysicalDensity (N := N) s σ) := by
  intro k w
  have hc (i : Fin N) : Complex.cos (complexToroidalTranslation k w i) = Complex.cos (w i) :=
    Complex.cos_add_int_mul_two_pi (w i) (k i)
  have he (i : Fin N) : Complex.exp (complexToroidalTranslation k w i * Complex.I) =
      Complex.exp (w i * Complex.I) := by
    have hh : complexToroidalTranslation k w i * Complex.I =
        w i * Complex.I + (k i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      unfold complexToroidalTranslation
      ring
    rw [hh, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [isotropicBarePhysicalDensity, isotropicInteriorRoot, isotropicDispersion, hc, he]

theorem homotopyPulledDensity_at_zero {N : ℕ} (η τ : ℝ)
    (F : (Fin N → ℂ) → ℂ) (θ : Fin N → ℝ) :
    homotopyPulledDensity η τ F (0, θ) = F (fun i => (θ i : ℂ)) := by
  have hM : actualBalancedJacobian η τ 0 θ = LinearMap.id := by
    ext v i
    simp [actualBalancedJacobian, balancedAngularJacobian, balancedDisplacementDifferential]
  have hχ : actualHomotopyAngle η τ 0 θ = fun i => (θ i : ℂ) := by
    funext i
    simp [actualHomotopyAngle_affine_time]
  rw [homotopyPulledDensity_actual, hM, hχ, LinearMap.det_id, one_mul]

/-- The actual complete physical deformation, with all regularity
hypotheses internally discharged. The size precedes N, the physical
parameter, the signed kernel and every constrained mean. -/
theorem exists_full_physical_balanced_deformation (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), ∀ τ ∈ Icc 0 δ,
      ∀ (s : ℂ), 0 < s.im → ∀ (σ : ℂ), ‖σ‖ ≤ 1 → ∀ a : ℝ,
      (∫ x in angularIntegrationBox (n + 1),
        (actualBalancedJacobian η τ 1 (affineConstraintAngles a x)).det *
          isotropicBarePhysicalDensity s σ (actualHomotopyAngle η τ 1 (affineConstraintAngles a x))) =
        ∫ x in angularIntegrationBox (n + 1),
          isotropicBarePhysicalDensity s σ (fun i => (affineConstraintAngles a x i : ℂ)) := by
  obtain ⟨δ, hδ, hdef⟩ := exists_balanced_constrained_integral_invariance η
  refine ⟨δ, hδ, ?_⟩
  intro n τ hτ s hs σ hσ a
  have hh := hdef n τ hτ a (isotropicBarePhysicalDensity s σ)
    (isotropicBarePhysicalDensity_periodic s σ)
    (fun ξ hξ θ => isotropicBarePhysicalDensity_analyticAt (by omega) s σ hσ _
      (fun i => actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i))
  simp only [balancedConstrainedIntegral, homotopyPulledDensity_at_zero] at hh
  simpa only [homotopyPulledDensity_actual] using hh

end IsingBulk.AnisoF002.Isotropic
