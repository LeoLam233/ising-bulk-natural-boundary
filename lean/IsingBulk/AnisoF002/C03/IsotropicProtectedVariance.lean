import IsingBulk.AnisoF002.C03.IsotropicActualJacobian
import IsingBulk.AnisoF002.C03.IsotropicProtectedSecants

/-!
# Quantitative actual variance and protected joint secant control

The coercivity applies to the actual balanced contour. The secant
Lipschitz estimate is joint in the parameter and both coordinates, on
one convex protected domain chosen before N. It preserves the common
parameter cancellation needed by the sharp covariance polydisk.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem rightPairParameterSegment_convex (S : ℝ) : Convex ℝ (rightPairParameterSegment S) := by
  have hi := ((convex_Icc (-rightBranchEndpoint S) (rightBranchEndpoint S)).linear_image
    Complex.ofRealCLM.toLinearMap)
  exact (convex_singleton (S : ℂ)).prod (hi.prod hi)

theorem exists_rightFirstSecant_joint_lipschitz (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧
      ∀ p ∈ thickening r (rightPairParameterSegment S),
      ∀ q ∈ thickening r (rightPairParameterSegment S),
        ‖jointFirstSecant explicitRightInverse q - jointFirstSecant explicitRightInverse p‖ ≤
          L * ‖q - p‖ := by
  obtain ⟨r, _, hr, _, _, hfirst, _, _, _, hjets⟩ :=
    exists_right_secants_protected_neighborhood S hS
  obtain ⟨C, _, _, hC, _, _⟩ := hjets 1
  let L := max 1 C
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hm : ∀ p ∈ thickening r (rightPairParameterSegment S),
      p ∈ cthickening r (rightPairParameterSegment S) :=
    fun _ hp => thickening_subset_cthickening r _ hp
  refine ⟨r, L, hr, hL, ?_⟩
  intro p hp q hq
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (fun z hz => (hfirst z (hm z hz)).differentiableAt)
    (fun z hz => ?_) ((rightPairParameterSegment_convex S).thickening r) hp hq
  have hz := hC z (hm z hz)
  rw [norm_iteratedFDeriv_one] at hz
  exact hz.trans (le_max_right _ _)

theorem jointFirstSecant_difference (U : ℂ × ℂ → ℂ) (s a b : ℂ) :
    U (s, a) - U (s, b) = (a - b) * jointFirstSecant U (s, a, b) := by
  simpa only [jointFirstSecant, smul_eq_mul] using (sub_smul_dslope (fun z => U (s, z)) b a).symm

/-- A common parameter perturbation changes an inverse difference by
the coordinate separation times the parameter increment. No separate
O(parameter increment) term is introduced for the two particles. -/
theorem inverse_common_parameter_difference_bound (U : ℂ × ℂ → ℂ)
    (s s' a b : ℂ) (L : ℝ)
    (hsec : ‖jointFirstSecant U (s', a, b) - jointFirstSecant U (s, a, b)‖ ≤
      L * ‖s' - s‖) :
    ‖(U (s', a) - U (s', b)) - (U (s, a) - U (s, b))‖ ≤
      L * ‖a - b‖ * ‖s' - s‖ := by
  rw [jointFirstSecant_difference U s' a b, jointFirstSecant_difference U s a b,
    ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left hsec (norm_nonneg _)).trans_eq (by ring)

/-- The actual complete bilinear variance dominates half the real
angular pair energy, uniformly before every particle number. -/
theorem exists_actual_variance_coercivity (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (1 / 2 : ℝ) * realPairEnergy θ ≤
          (pairVariance (actualHomotopyAngle η τ ξ θ)).re := by
  obtain ⟨L, hL, _, _, hpL, hmL⟩ := actual_bump_global_first_bounds η
  let δ := 1 / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδL : δ * L = 1 / 8 := by dsimp [δ]; field_simp
  refine ⟨δ, hδ, ?_⟩
  intro N hN τ hτ ξ hξ θ
  have hs : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hsL : (ξ * τ) * L ≤ 1 / 8 := by
    have hξτ : ξ * τ ≤ τ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξ.2 hτ.1
    exact (mul_le_mul_of_nonneg_right (hξτ.trans hτ.2) hL.le).trans_eq hδL
  have hsmall : ((ξ * τ) * (L + L)) ^ 2 ≤ 1 / 2 := by
    have hnonneg : 0 ≤ (ξ * τ) * L := mul_nonneg hs hL.le
    nlinarith
  have hcard : 0 < Fintype.card (Fin N) := by simpa using hN
  have hc := contour_variance_coercive θ
    (balancedShift ((ξ * τ) / Fintype.card (Fin N))
      (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k)))
    ((ξ * τ) * (L + L))
    (balancedShift_pair_sq_bound θ
      (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))
      (ξ * τ) L L hcard hs hL.le hL.le
      (fun k => upperPeriodicBump_bounds η (θ k)) (fun k => lowerPeriodicBump_bounds η (θ k))
      (fun k l => hpL (θ k) (θ l)) (fun k l => hmL (θ k) (θ l)))
  have he : ξ * (τ / (Fintype.card (Fin N) : ℝ)) = (ξ * τ) / Fintype.card (Fin N) := by ring
  change (1 / 2 : ℝ) * realPairEnergy θ ≤
    (pairVariance (contourCoordinate θ (balancedShift (ξ * (τ / Fintype.card (Fin N)))
      (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))))).re
  rw [he]
  exact (mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤
    1 - ((ξ * τ) * (L + L)) ^ 2) (realPairEnergy_nonneg θ)).trans hc

theorem complex_square_perturbation_bound (z w : ℂ) (d ε : ℝ)
    (hz : ‖z‖ ≤ d) (hw : ‖w - z‖ ≤ ε) :
    ‖w ^ 2 - z ^ 2‖ ≤ ε * (2 * d + ε) := by
  have he : w ^ 2 - z ^ 2 = (w - z) * (2 * z + (w - z)) := by ring
  rw [he, norm_mul]
  have hn : ‖2 * z + (w - z)‖ ≤ 2 * d + ε := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_two]
    linarith
  have hε : 0 ≤ ε := (norm_nonneg (w - z)).trans hw
  exact mul_le_mul hw hn (norm_nonneg _) hε

theorem pairVariance_perturbation_bound_c03 {N : ℕ} (u v : Fin N → ℂ) (d ε : ℝ)
    (hu : ∀ i j, ‖u i - u j‖ ≤ d)
    (hv : ∀ i j, ‖(v i - v j) - (u i - u j)‖ ≤ ε) :
    ‖pairVariance v - pairVariance u‖ ≤ (N : ℝ) ^ 2 / 2 * ε * (2 * d + ε) := by
  have he : pairVariance v - pairVariance u =
      (1 / 2 : ℂ) * ∑ i, ∑ j, ((v i - v j) ^ 2 - (u i - u j) ^ 2) := by
    simp only [pairVariance, Finset.sum_sub_distrib, mul_sub]
  rw [he, norm_mul]
  rw [norm_div, norm_one, Complex.norm_two]
  have hsum : ‖∑ i, ∑ j, ((v i - v j) ^ 2 - (u i - u j) ^ 2)‖ ≤
      (N : ℝ) ^ 2 * (ε * (2 * d + ε)) := by
    calc
      _ ≤ ∑ i, ∑ j, ‖(v i - v j) ^ 2 - (u i - u j) ^ 2‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, ε * (2 * d + ε) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact complex_square_perturbation_bound (u i - u j) (v i - v j) d ε (hu i j) (hv i j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have heR : (1 / 2 : ℝ) * ((N : ℝ) ^ 2 * (ε * (2 * d + ε))) =
      (N : ℝ) ^ 2 / 2 * ε * (2 * d + ε) := by ring
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq heR

end IsingBulk.AnisoF002.Isotropic
