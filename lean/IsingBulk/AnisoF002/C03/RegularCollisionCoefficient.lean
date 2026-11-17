import IsingBulk.AnisoF002.C03.RegularCollisionDominated
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact local coefficient normalization and derivative scaling

The local integral is taken from the actual normalized particle
coefficient.  Its probability-angle measure is converted to the original
independent-coordinate Lebesgue measure, with precisely the factorial
and (2 pi)^(N-1) factor.  The s-scaling below is a genuine measure change.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def regularCoefficientNormalization (n : ℕ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ * (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹

theorem regularCoefficientNormalization_ne_zero (n : ℕ) :
    regularCoefficientNormalization n ≠ 0 := by
  apply mul_ne_zero
  · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (n + 1))
  · exact inv_ne_zero (by exact_mod_cast pow_ne_zero n (mul_ne_zero (by norm_num) Real.pi_ne_zero))

theorem regularCoefficientNormalization_eq (n : ℕ) :
    regularCoefficientNormalization n =
      1 / (((n + 1).factorial : ℂ) * (2 * (Real.pi : ℂ)) ^ n) := by
  simp only [regularCoefficientNormalization, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_ofNat, one_div, mul_inv_rev]
  ring

theorem collisionBall_subset_angularBox {n : ℕ} {delta : ℝ} (hd : delta ≤ Real.pi) :
    Metric.ball (0 : Fin n → ℝ) delta ⊆ regularAngularBox n := by
  intro q hq
  have hn : ‖q‖ < delta := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  have hi (i : Fin n) : |q i| ≤ Real.pi := by
    have hqi : |q i| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q i
    exact hqi.trans (hn.le.trans hd)
  exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem regularAngularProbability_local_integral {n : ℕ} {delta : ℝ}
    (hd : delta ≤ Real.pi) (f : (Fin n → ℝ) → ℂ) :
    (∫ q in Metric.ball 0 delta, f q ∂regularAngularProbability n) =
      (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ * ∫ q in Metric.ball 0 delta, f q := by
  rw [regularAngularProbability, Measure.restrict_smul,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
    inter_eq_left.mpr (collisionBall_subset_angularBox hd), integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal
      (pow_nonneg (show (0 : ℝ) ≤ 2 * Real.pi by positivity) n),
    Complex.real_smul, Complex.ofReal_inv]

theorem collisionScaledLocal_integral_scaling {n : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (j : ℕ) (delta : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ q : Fin n → ℝ, collisionScaledLocal b a j delta s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) /
        (s : ℂ) ^ n * ∫ q in Metric.ball (0 : Fin n → ℝ) delta,
          iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
            (((s ^ 2 : ℝ) : ℂ) * Complex.I) := by
  let F : (Fin n → ℝ) → ℂ := fun q =>
    if ‖q‖ < delta then iteratedDeriv j
      (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
        (((s ^ 2 : ℝ) : ℂ) * Complex.I) else 0
  have he : (fun q : Fin n → ℝ => collisionScaledLocal b a j delta s q) =
      fun q => ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) * F (s • q) := by
    funext q
    by_cases hq : ‖s • q‖ < delta
    · simp only [collisionScaledLocal, F, ite_eq_left hq, collisionScaledJet]
      congr 2
      funext u
      rw [show s • q = (fun i => s * q i) by rfl, flatConstrainedAngles_mul]
    · simp only [collisionScaledLocal, F, ite_eq_right hq, mul_zero]
  have hF : F = (Metric.ball (0 : Fin n → ℝ) delta).indicator
      (fun q => iteratedDeriv j
        (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
          (((s ^ 2 : ℝ) : ℂ) * Complex.I)) := by
    funext q
    simp only [F, Set.indicator, Metric.mem_ball, dist_zero_right]
  rw [he, integral_const_mul, Measure.integral_comp_smul_of_nonneg volume F s (hR := hs),
    Module.finrank_pi, Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, hF, integral_indicator Metric.isOpen_ball.measurableSet]
  ring

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem restricted_particle_iteratedDeriv (n j : ℕ) (S : Set (Fin n → ℝ)) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (fun u => ((n + 1).factorial : ℂ)⁻¹ *
      ∫ q in S, edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q)
        ∂regularAngularProbability n) ((eps : ℂ) * Complex.I) =
      ((n + 1).factorial : ℂ)⁻¹ * ∫ q in S,
        iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
          ((eps : ℂ) * Complex.I) ∂regularAngularProbability n := by
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have h := iteratedDeriv_integral_of_joint_analytic
    (μ := (regularAngularProbability n).restrict S)
    (f := edgeJointDensity (affineEdgeCenter b) a)
    (g := fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q))
    (regularAngularBox_compact n) (ae_restrict_of_ae (regularAngularProbability_ae_mem n))
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n))
    (fun q _ => d.jointDensity_analytic_inward (Nat.succ_pos n) he he0 (flatConstrainedAngles q)) j
  simpa only [edgeJointDensity_real] using h

theorem localCoefficient_jet_volume (n j : ℕ) {delta eps : ℝ}
    (hd : delta ≤ Real.pi) (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta)
      ((eps : ℂ) * Complex.I) =
      regularCoefficientNormalization n * ∫ q in Metric.ball (0 : Fin n → ℝ) delta,
        iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q))
          ((eps : ℂ) * Complex.I) := by
  unfold edgeLocalCollisionCoefficient
  rw [d.restricted_particle_iteratedDeriv n j _ he he0,
    regularAngularProbability_local_integral hd]
  exact (mul_assoc _ _ _).symm

theorem localCoefficient_scaled_integral (n j : ℕ) {delta s : ℝ}
    (hd : delta ≤ Real.pi) (hs : 0 < s) (hs0 : s ^ 2 ≤ d.eps0) :
    regularCoefficientNormalization n *
      (∫ q : Fin n → ℝ, collisionScaledLocal b a j delta s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (n + 2 * (n + 1).choose 2)) *
        iteratedDeriv j (edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta)
          (((s ^ 2 : ℝ) : ℂ) * Complex.I) := by
  rw [collisionScaledLocal_integral_scaling b a j delta hs.le,
    d.localCoefficient_jet_volume n j hd (sq_pos_of_pos hs) hs0,
    pow_add (s : ℂ) n (2 * (n + 1).choose 2)]
  field_simp

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
