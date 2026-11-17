import IsingBulk.AnisoF002.C03.IsotropicSharpPerturbation
import IsingBulk.AnisoF002.C03.IsotropicCovarianceDisks

/-!
# Quantitative controls for the sharp shell covariance disks

The common inverse domain supplies the analytic secants and their
uniform inverse denominator. The estimates retain the coordinate
scale in the numerator and the common-parameter cancellation in the
variance, rather than bounding either by a fixed nonzero constant.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_right_sharp_covariance_primitives (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧
      AnalyticOnNhd ℂ explicitRightInverse (cthickening r (rightParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointFirstSecant explicitRightInverse) (cthickening r (rightPairParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointSecondSecant explicitRightInverse) (cthickening r (rightPairParameterSegment S)) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S), jointSecondSecant explicitRightInverse q ≠ 0) ∧
      (∀ q ∈ cthickening r (rightParameterSegment S), ‖jointParameterDerivative explicitRightInverse q‖ ≤ C) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S), ‖(jointSecondSecant explicitRightInverse q)⁻¹‖ ≤ C) ∧
      ∀ p ∈ thickening r (rightPairParameterSegment S),
      ∀ q ∈ thickening r (rightPairParameterSegment S),
        ‖jointFirstSecant explicitRightInverse q - jointFirstSecant explicitRightInverse p‖ ≤ C * ‖q - p‖ := by
  obtain ⟨rP, CP, hrP, hCP, hU, hfirst, hsecond, hne, _, hP, _, _⟩ :=
    exists_right_covariance_primitive_control S hS
  obtain ⟨rL, L, hrL, hL, hLip⟩ := exists_rightFirstSecant_joint_lipschitz S hS
  obtain ⟨rE, c, hrE, hc, _, _, _, _, hlow, _⟩ := exists_right_secants_protected_neighborhood S hS
  let r := min rP (min rL rE)
  let C := max CP (max L c⁻¹)
  have hr : 0 < r := lt_min hrP (lt_min hrL hrE)
  have hrP' : r ≤ rP := min_le_left _ _
  have hrL' : r ≤ rL := (min_le_right _ _).trans (min_le_left _ _)
  have hrE' : r ≤ rE := (min_le_right _ _).trans (min_le_right _ _)
  have hC : 1 ≤ C := hCP.trans (le_max_left _ _)
  refine ⟨r, C, hr, hC,
    (fun q hq => hU q (cthickening_mono hrP' _ hq)),
    (fun q hq => hfirst q (cthickening_mono hrP' _ hq)),
    (fun q hq => hsecond q (cthickening_mono hrP' _ hq)),
    (fun q hq => hne q (cthickening_mono hrP' _ hq)),
    (fun q hq => (hP q (cthickening_mono hrP' _ hq)).trans (le_max_left _ _)), ?_, ?_⟩
  · intro q hq
    have hn : c ≤ ‖jointSecondSecant explicitRightInverse q‖ :=
      (hlow q (cthickening_mono hrE' _ hq)).trans (Complex.re_le_norm _)
    rw [norm_inv]
    exact (inv_anti₀ hc hn).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro p hp q hq
    exact (hLip p (thickening_mono hrL' _ hp) q (thickening_mono hrL' _ hq)).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))

theorem pairVariance_shell_stability {N : ℕ} (hN : 0 < N) (u v : Fin N → ℂ)
    (r m : ℝ) (hr : 0 < r) (hm : 0 ≤ m) (hsmall : m ≤ 1 / 64)
    (hu : ∀ i j, ‖u i - u j‖ ≤ 4 * r)
    (hmove : ∀ i j, ‖(v i - v j) - (u i - u j)‖ ≤ m * r / (N : ℝ) ^ 2)
    (hD : r ^ 2 / 4 ≤ (pairVariance u).re) :
    ‖pairVariance v - pairVariance u‖ ≤ r ^ 2 / 8 ∧
      r ^ 2 / 8 ≤ ‖pairVariance v‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
  let e := m * r / (N : ℝ) ^ 2
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have her : e ≤ r := by
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    have hm1 : m ≤ 1 := by linarith only [hsmall]
    exact (mul_le_mul_of_nonneg_right hm1 hr.le).trans (by nlinarith only [hN2, hr])
  have hv := pairVariance_perturbation_bound_c03 u v (4 * r) e hu hmove
  have hvar : ‖pairVariance v - pairVariance u‖ ≤ r ^ 2 / 8 := by
    calc
      _ ≤ (N : ℝ) ^ 2 / 2 * e * (2 * (4 * r) + e) := hv
      _ ≤ (N : ℝ) ^ 2 / 2 * e * (9 * r) := by gcongr; linarith only [her]
      _ = (9 / 2 : ℝ) * m * r ^ 2 := by dsimp [e]; field_simp
      _ ≤ r ^ 2 / 8 := by
        have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg r)
        nlinarith only [hh, sq_nonneg r]
  refine ⟨hvar, ?_⟩
  have hcenter := hD.trans (Complex.re_le_norm _)
  have htri := norm_le_norm_sub_add (pairVariance u) (pairVariance v)
  rw [norm_sub_rev] at htri
  linarith only [hcenter, htri, hvar]

theorem covariancePair_shell_bound (D : Set (ℂ × ℂ × ℂ))
    (L K A E t Δ ρ : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hΔ : 0 ≤ Δ) (hρΔ : ρ ≤ Δ) (hΔt : Δ ≤ t)
    (hLip : ∀ p ∈ D, ∀ q ∈ D,
      ‖jointFirstSecant explicitRightInverse q - jointFirstSecant explicitRightInverse p‖ ≤ L * ‖q - p‖)
    (s s' a a' b b' : ℂ) (hdiag : (s, a, a) ∈ D) (hpair : (s', a', b') ∈ D)
    (hs : ‖s' - s‖ ≤ ρ) (ha : ‖a' - a‖ ≤ ρ) (hb : ‖b' - b‖ ≤ ρ)
    (hab : ‖a - b‖ ≤ A * Δ)
    (hUa : ‖deriv (fun z => explicitRightInverse (s, z)) a‖ ≤ K * t)
    (hEinv : ‖(jointSecondSecant explicitRightInverse (s', a', b'))⁻¹‖ ≤ E) :
    ‖jointCovariancePair (s', a', b')‖ ≤
      ((A + 2) * (K + L * (A + 1)) ^ 2 * E) * t ^ 2 * Δ := by
  have hΔA : Δ ≤ (A + 1) * Δ := by nlinarith only [hA, hΔ]
  have hba : ‖b' - a‖ ≤ (A + 1) * Δ := by
    have hh : ‖b' - a‖ ≤ ‖b' - b‖ + ‖b - a‖ := by
      simpa only [dist_eq_norm] using dist_triangle b' b a
    rw [norm_sub_rev b a] at hh
    linarith only [hh, hb, hab, hρΔ]
  have htriple := triple_complex_norm_sub_le s s' a a' a b' ((A + 1) * Δ)
    (hs.trans (hρΔ.trans hΔA)) (ha.trans (hρΔ.trans hΔA)) hba
  have hsec := (hLip (s, a, a) hdiag (s', a', b') hpair).trans
    (mul_le_mul_of_nonneg_left htriple hL)
  have hbase : jointFirstSecant explicitRightInverse (s, a, a) =
      deriv (fun z => explicitRightInverse (s, z)) a := by simp only [jointFirstSecant, dslope_same]
  have hsecBound : ‖jointFirstSecant explicitRightInverse (s', a', b')‖ ≤ (K + L * (A + 1)) * t := by
    have hh := norm_le_norm_sub_add (jointFirstSecant explicitRightInverse (s', a', b'))
      (jointFirstSecant explicitRightInverse (s, a, a))
    rw [hbase] at hh hsec
    have hscale := mul_le_mul_of_nonneg_left hΔt (mul_nonneg hL (by linarith only [hA] : 0 ≤ A + 1))
    nlinarith only [hh, hsec, hUa, hscale]
  have hgap : ‖a' - b'‖ ≤ (A + 2) * Δ := by
    have he : a' - b' = ((a' - a) + (a - b)) + (b - b') := by ring
    have hh : ‖a' - b'‖ ≤ (‖a' - a‖ + ‖a - b‖) + ‖b - b'‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [norm_sub_rev b b'] at hh
    linarith only [hh, ha, hb, hab, hρΔ]
  rw [jointCovariancePair, norm_div, norm_mul, norm_pow, div_eq_mul_inv]
  have hsecSq : ‖jointFirstSecant explicitRightInverse (s', a', b')‖ ^ 2 ≤
      ((K + L * (A + 1)) * t) ^ 2 := by gcongr
  have hE' : ‖jointSecondSecant explicitRightInverse (s', a', b')‖⁻¹ ≤ E := by
    simpa only [norm_inv] using hEinv
  calc
    _ ≤ (((A + 2) * Δ) * (((K + L * (A + 1)) * t) ^ 2)) * E := by gcongr
    _ = _ := by ring

theorem rightCovarianceField_norm_bound_general {N : ℕ} (q : ℂ × (Fin N → ℂ))
    (P H d : ℝ) (hP0 : 0 ≤ P) (hH0 : 0 ≤ H) (hd : 0 < d)
    (hP : ∀ i, ‖jointParameterDerivative explicitRightInverse (q.1, q.2 i)‖ ≤ P)
    (hH : ∀ i j, ‖jointCovariancePair (q.1, q.2 i, q.2 j)‖ ≤ H)
    (hD : d ≤ ‖pairVariance (fun i => explicitRightInverse (q.1, q.2 i))‖) :
    ‖rightCovarianceField q.1 q.2‖ ≤ P * H * (N : ℝ) ^ 2 / d := by
  have hA : ‖rightCovarianceAmplitude q.1 q.2‖ ≤ (N : ℝ) * P := by
    unfold rightCovarianceAmplitude
    rw [norm_neg]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hP i)).trans_eq (by simp))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hG : ‖∑ j, analyticSecantPair (fun z => explicitRightInverse (q.1, z)) q.2 i j‖ ≤
      (N : ℝ) * H :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hH i j)).trans_eq (by simp))
  change ‖rightCovarianceAmplitude q.1 q.2 *
    (∑ j, analyticSecantPair (fun z => explicitRightInverse (q.1, z)) q.2 i j) /
      pairVariance (fun j => explicitRightInverse (q.1, q.2 j))‖ ≤ _
  rw [norm_div, norm_mul]
  have hn := mul_le_mul hA hG (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hP0)
  exact (div_le_div₀ (by positivity) hn hd hD).trans_eq (by ring)

end IsingBulk.AnisoF002.Isotropic
