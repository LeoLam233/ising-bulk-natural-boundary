import IsingBulk.AnisoF002.C03.IsotropicProtectedVariance
import IsingBulk.AnisoF002.C03.IsotropicAnalyticCovariance
import IsingBulk.AnisoF002.C03.IsotropicRetainedGaussianJets

/-!
# Uniform primitives for the actual covariance field

The inverse, its parameter derivative, and the filled pair coefficient
are bounded on common compact neighborhoods selected before N. The
joint inverse Lipschitz estimate is proved on the same convex domain.
These data support variance-protected complex disks, including every
proper partial diagonal.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def jointCovariancePair (q : ℂ × ℂ × ℂ) : ℂ :=
  (q.2.1 - q.2.2) * (jointFirstSecant explicitRightInverse q) ^ 2 /
    jointSecondSecant explicitRightInverse q

theorem jointCovariancePair_eq {ι : Type*} (s : ℂ) (v : ι → ℂ) (i j : ι) :
    jointCovariancePair (s, v i, v j) =
      analyticSecantPair (fun z => explicitRightInverse (s, z)) v i j := rfl

theorem jointCovariancePair_analyticAt (q : ℂ × ℂ × ℂ)
    (h₁ : AnalyticAt ℂ (jointFirstSecant explicitRightInverse) q)
    (h₂ : AnalyticAt ℂ (jointSecondSecant explicitRightInverse) q)
    (hne : jointSecondSecant explicitRightInverse q ≠ 0) :
    AnalyticAt ℂ jointCovariancePair q :=
  (((analyticAt_fst.comp analyticAt_snd).sub (analyticAt_snd.comp analyticAt_snd)).mul
    (h₁.pow 2)).div h₂ hne

/-- All constants and domains here precede particle number. In
particular the pair coefficient is filled, not divided by a pair gap. -/
theorem exists_right_covariance_primitive_control (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧
      AnalyticOnNhd ℂ explicitRightInverse (cthickening r (rightParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointFirstSecant explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointSecondSecant explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S),
        jointSecondSecant explicitRightInverse q ≠ 0) ∧
      (∀ q ∈ cthickening r (rightParameterSegment S), ‖explicitRightInverse q‖ ≤ C) ∧
      (∀ q ∈ cthickening r (rightParameterSegment S),
        ‖jointParameterDerivative explicitRightInverse q‖ ≤ C) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S), ‖jointCovariancePair q‖ ≤ C) ∧
      ∀ p ∈ thickening r (rightParameterSegment S),
      ∀ q ∈ thickening r (rightParameterSegment S),
        ‖explicitRightInverse q - explicitRightInverse p‖ ≤ C * ‖q - p‖ := by
  obtain ⟨r₁, _, hr₁, _, _, _, hU, _, hjets⟩ :=
    exists_right_inverse_common_convex_neighborhood S hS
  obtain ⟨r₂, c, hr₂, hc, _, hfirst, hsecond, _, hlower, _⟩ :=
    exists_right_secants_protected_neighborhood S hS
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hr1 : r ≤ r₁ := min_le_left _ _
  have hr2 : r ≤ r₂ := min_le_right _ _
  have hU' : AnalyticOnNhd ℂ explicitRightInverse (cthickening r (rightParameterSegment S)) :=
    fun q hq => hU q (cthickening_mono hr1 _ hq)
  have hfirst' : AnalyticOnNhd ℂ (jointFirstSecant explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) :=
    fun q hq => hfirst q (cthickening_mono hr2 _ hq)
  have hsecond' : AnalyticOnNhd ℂ (jointSecondSecant explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) :=
    fun q hq => hsecond q (cthickening_mono hr2 _ hq)
  have hne : ∀ q ∈ cthickening r (rightPairParameterSegment S),
      jointSecondSecant explicitRightInverse q ≠ 0 := by
    intro q hq hz
    have hl := hlower q (cthickening_mono hr2 _ hq)
    rw [hz, Complex.zero_re] at hl
    linarith
  have hP : AnalyticOnNhd ℂ (jointParameterDerivative explicitRightInverse)
      (cthickening r (rightParameterSegment S)) :=
    fun q hq => jointParameterDerivative_analyticAt _ q (hU' q hq)
  have hH : AnalyticOnNhd ℂ jointCovariancePair
      (cthickening r (rightPairParameterSegment S)) :=
    fun q hq => jointCovariancePair_analyticAt q (hfirst' q hq) (hsecond' q hq) (hne q hq)
  obtain ⟨C₀, hC₀⟩ := hjets 0
  obtain ⟨C₁, hC₁⟩ := hjets 1
  obtain ⟨CP, hCP⟩ := (rightParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    hP.continuousOn
  obtain ⟨CH, hCH⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    hH.continuousOn
  let C := max 1 (max C₀ (max C₁ (max CP CH)))
  have hC : 1 ≤ C := le_max_left _ _
  have h0 : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h1 : C₁ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hP' : CP ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hH' : CH ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨r, C, hr, hC, hU', hfirst', hsecond', hne, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have h := hC₀ q (cthickening_mono hr1 _ hq)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans h0
  · intro q hq
    exact (hCP q hq).trans hP'
  · intro q hq
    exact (hCH q hq).trans hH'
  · intro p hp q hq
    apply Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℂ) (fun z hz => (hU' z (thickening_subset_cthickening r _ hz)).differentiableAt)
      (fun z hz => ?_) ((rightParameterSegment_convex S).thickening r) hp hq
    have h := hC₁ z (cthickening_mono hr1 _ (thickening_subset_cthickening r _ hz))
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans h1

theorem pairVariance_lipschitz_bound {N : ℕ} (u v : Fin N → ℂ) (C ρ : ℝ)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hu : ∀ i, ‖u i‖ ≤ C) (hv : ∀ i, ‖v i‖ ≤ C)
    (hmove : ∀ i, ‖v i - u i‖ ≤ C * ρ) :
    ‖pairVariance v - pairVariance u‖ ≤ 4 * C ^ 2 * (N : ℝ) ^ 2 * ρ := by
  have hpair (i j : Fin N) :
      ‖(v i - v j) ^ 2 - (u i - u j) ^ 2‖ ≤ 8 * C ^ 2 * ρ := by
    have hdiff : ‖(v i - v j) - (u i - u j)‖ ≤ 2 * C * ρ := by
      have he : (v i - v j) - (u i - u j) = (v i - u i) - (v j - u j) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith [hmove i, hmove j])
    have hsum : ‖(v i - v j) + (u i - u j)‖ ≤ 4 * C := by
      have huij := norm_sub_le (u i) (u j)
      have hvij := norm_sub_le (v i) (v j)
      exact (norm_add_le _ _).trans (by linarith [hu i, hu j, hv i, hv j])
    have he : (v i - v j) ^ 2 - (u i - u j) ^ 2 =
        ((v i - v j) - (u i - u j)) * ((v i - v j) + (u i - u j)) := by ring
    rw [he, norm_mul]
    calc
      _ ≤ (2 * C * ρ) * (4 * C) :=
        mul_le_mul hdiff hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have he : pairVariance v - pairVariance u =
      (1 / 2 : ℂ) * ∑ i, ∑ j, ((v i - v j) ^ 2 - (u i - u j) ^ 2) := by
    simp only [pairVariance, Finset.sum_sub_distrib, mul_sub]
  rw [he, norm_mul, norm_div, norm_one, Complex.norm_two]
  have hsum : ‖∑ i, ∑ j, ((v i - v j) ^ 2 - (u i - u j) ^ 2)‖ ≤
      (N : ℝ) ^ 2 * (8 * C ^ 2 * ρ) := by
    calc
      _ ≤ ∑ i, ∑ j, ‖(v i - v j) ^ 2 - (u i - u j) ^ 2‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, 8 * C ^ 2 * ρ :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)

theorem rightCovarianceField_norm_bound {N : ℕ} (q : ℂ × (Fin N → ℂ)) (C d : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d)
    (hP : ∀ i, ‖jointParameterDerivative explicitRightInverse (q.1, q.2 i)‖ ≤ C)
    (hH : ∀ i j, ‖jointCovariancePair (q.1, q.2 i, q.2 j)‖ ≤ C)
    (hD : d ≤ ‖pairVariance (fun i => explicitRightInverse (q.1, q.2 i))‖) :
    ‖rightCovarianceField q.1 q.2‖ ≤ C ^ 2 * (N : ℝ) ^ 2 / d := by
  have hA : ‖rightCovarianceAmplitude q.1 q.2‖ ≤ (N : ℝ) * C := by
    unfold rightCovarianceAmplitude
    rw [norm_neg]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hP i)).trans_eq (by simp))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hG : ‖∑ j, analyticSecantPair (fun z => explicitRightInverse (q.1, z)) q.2 i j‖ ≤
      (N : ℝ) * C :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hH i j)).trans_eq (by simp))
  change ‖rightCovarianceAmplitude q.1 q.2 *
    (∑ j, analyticSecantPair (fun z => explicitRightInverse (q.1, z)) q.2 i j) /
      pairVariance (fun j => explicitRightInverse (q.1, q.2 j))‖ ≤ _
  rw [norm_div, norm_mul]
  have hn : ‖rightCovarianceAmplitude q.1 q.2‖ *
      ‖∑ j, analyticSecantPair (fun z => explicitRightInverse (q.1, z)) q.2 i j‖ ≤
      ((N : ℝ) * C) * ((N : ℝ) * C) :=
    mul_le_mul hA hG (norm_nonneg _) (by positivity)
  calc
    _ ≤ (((N : ℝ) * C) * ((N : ℝ) * C)) / d :=
      div_le_div₀ (by positivity) hn hd hD
    _ = _ := by ring

end IsingBulk.AnisoF002.Isotropic
