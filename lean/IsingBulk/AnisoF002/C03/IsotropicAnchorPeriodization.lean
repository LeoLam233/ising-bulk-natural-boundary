import IsingBulk.AnisoF002.C03.IsotropicCompactAnchorCutoff

/-!
# Exact finite periodization of every original lower anchor

Only the eliminated angle is shifted after the independent variables
are placed in one full shifted period. The actual lower population and
ordered telescoping prefix are retained. All nonzero integer lifts are
included in the same explicit finite mean set.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.NegativeHT IsingBulk.AnisoF002.RegularTail.C03

abbrev anchorIntegrationBox (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  Icc (fun _ => -Real.pi - ρ) (fun _ => Real.pi - ρ)

theorem angularIntegrationBox_eq_anchor_integral {n : ℕ} (ρ : ℝ)
    (F : (Fin n → ℝ) → ℂ) (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) :
    (∫ x in angularIntegrationBox n, F x) = ∫ x in anchorIntegrationBox n ρ, F x := by
  have he : windingPeriodBox n (fun _ => -Real.pi - ρ) =ᵐ[volume] anchorIntegrationBox n ρ := by
    rw [volume_pi]
    simpa only [windingPeriodBox, anchorIntegrationBox,
      show -Real.pi - ρ + 2 * Real.pi = Real.pi - ρ by ring] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
        (f := fun _ => -Real.pi - ρ) (g := fun _ => Real.pi - ρ))
  rw [angularIntegrationBox_eq_centered_integral F hF,
    ← setIntegral_congr_set (windingPeriodBox_centered_ae n), ← setIntegral_congr_set he]
  exact windingPeriodBox_integral_eq n F hF _ _

theorem actualLowerCompactAnchorCutoff_zero_coordinate {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) {N : ℕ} (i j : Fin N) (θ : Fin N → ℝ)
    (hj : θ j ≤ -Real.pi - ρ ∨ ρ ≤ θ j) :
    actualLowerCompactAnchorCutoff η b δ ρ i θ = 0 := by
  have hp : compactLowerWindowProduct ρ N θ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [compactLowerWindow_zero hρ hj, Complex.ofReal_zero]
  rw [actualLowerCompactAnchorCutoff, hp, mul_zero]

theorem actualLowerCompactAnchorCutoff_nonzero_angles {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) {N : ℕ} (i : Fin N) (θ : Fin N → ℝ)
    (hn : actualLowerCompactAnchorCutoff η b δ ρ i θ ≠ 0) :
    ∀ j, θ j ∈ Ioo (-Real.pi - ρ) ρ := by
  intro j
  constructor
  · by_contra hh
    exact hn (actualLowerCompactAnchorCutoff_zero_coordinate hρ η b δ i j θ
      (Or.inl (le_of_not_gt hh)))
  · by_contra hh
    exact hn (actualLowerCompactAnchorCutoff_zero_coordinate hρ η b δ i j θ
      (Or.inr (le_of_not_gt hh)))

theorem actualLowerCompactAnchorCutoff_admissible {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) {n : ℕ} (i : Fin (n + 1)) (a : ℝ) (x : Fin n → ℝ) (l : ℤ)
    (hn : actualLowerCompactAnchorCutoff η b δ ρ i
      (affineConstraintAngles (2 * Real.pi * l + a) x) ≠ 0) :
    l ∈ admissibleRightLifts (n + 1) Real.pi ρ a := by
  have ht := actualLowerCompactAnchorCutoff_nonzero_angles hρ η b δ i _ hn
  have hlo := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) => (ht j).1.le)
  have hup := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) => (ht j).2.le)
  rw [affineConstraintAngles_sum_c03, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hlo hup
  exact (admissibleRightLifts_mem_iff (n + 1) Real.pi ρ a l).mpr ⟨hlo, hup⟩

theorem actual_lower_anchor_finite_periodization {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (b δ : ℝ) {n : ℕ}
    (i : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℂ)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ)
    (a : ℝ) (x : Fin n → ℝ) (hx : x ∈ anchorIntegrationBox n ρ) :
    actualLowerAnchorCutoff η b δ ρ i (affineConstraintAngles a x) * F (affineConstraintAngles a x) =
      ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        actualLowerCompactAnchorCutoff η b δ ρ i (affineConstraintAngles (2 * Real.pi * l + a) x) *
          F (affineConstraintAngles (2 * Real.pi * l + a) x) := by
  obtain ⟨l₀, hl₀, huniq⟩ := existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos
    (a - ∑ j, x j) (-Real.pi - ρ)
  have hθ : ∀ j, affineConstraintAngles (2 * Real.pi * l₀ + a) x j ∈
      Icc (-Real.pi - ρ) (Real.pi - ρ) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last]
      simp only [mem_Ioc, zsmul_eq_mul] at hl₀
      exact ⟨by linarith [hl₀.1], by linarith [hl₀.2]⟩
    · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc]
      exact ⟨hx.1 k, hx.2 k⟩
  have hper (l : ℤ) : actualLowerAnchorCutoff η b δ ρ i
      (affineConstraintAngles (2 * Real.pi * l + a) x) * F (affineConstraintAngles (2 * Real.pi * l + a) x) =
        actualLowerAnchorCutoff η b δ ρ i (affineConstraintAngles a x) * F (affineConstraintAngles a x) := by
    rw [affineConstraintAngles_last_period, actualLowerAnchorCutoff_toroidal, hF]
  have hmain := (hper l₀).symm
  rw [← actualLowerCompactAnchorCutoff_eq_periodic hη hρ hρπ hgap b δ i _ hθ] at hmain
  rw [hmain]
  symm
  apply Finset.sum_eq_single l₀
  · intro l _ hl
    have hz : actualLowerCompactAnchorCutoff η b δ ρ i
        (affineConstraintAngles (2 * Real.pi * l + a) x) = 0 := by
      by_contra hn
      have hh := actualLowerCompactAnchorCutoff_nonzero_angles hρ η b δ i _ hn (Fin.last n)
      simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last] at hh
      apply hl
      apply huniq l
      simp only [mem_Ioc, zsmul_eq_mul]
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    rw [hz, zero_mul]
  · intro hl
    have hz : actualLowerCompactAnchorCutoff η b δ ρ i
        (affineConstraintAngles (2 * Real.pi * l₀ + a) x) = 0 := by
      by_contra hn
      exact hl (actualLowerCompactAnchorCutoff_admissible hρ η b δ i a x l₀ hn)
    rw [hz, zero_mul]

theorem actualLowerCompactAnchorCutoff_affine_zero_off_box {ρ : ℝ} (hρ : 0 < ρ)
    (hρπ : ρ ≤ Real.pi / 2) (η b δ a : ℝ) {n : ℕ} (i : Fin (n + 1))
    (x : Fin n → ℝ) (hx : x ∉ anchorIntegrationBox n ρ) :
    actualLowerCompactAnchorCutoff η b δ ρ i (affineConstraintAngles a x) = 0 := by
  by_contra hn
  have ht := actualLowerCompactAnchorCutoff_nonzero_angles hρ η b δ i _ hn
  apply hx
  constructor
  · intro j
    simpa only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc] using (ht j.castSucc).1.le
  · intro j
    have hj := (ht j.castSucc).2
    simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc] at hj
    linarith

theorem actual_lower_anchor_compact_integrable {ρ : ℝ} (hρ : 0 < ρ)
    (hρπ : ρ ≤ Real.pi / 2) (η b δ a : ℝ) {n : ℕ} (i : Fin (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℂ) (hc : Continuous F) :
    Integrable (fun x : Fin n → ℝ => actualLowerCompactAnchorCutoff η b δ ρ i
      (affineConstraintAngles a x) * F (affineConstraintAngles a x)) := by
  let f := fun x : Fin n → ℝ => actualLowerCompactAnchorCutoff η b δ ρ i
    (affineConstraintAngles a x) * F (affineConstraintAngles a x)
  have hf : Continuous f := ((actualLowerCompactAnchorCutoff_contDiff η b δ ρ i (k := 0)).continuous.mul hc).comp
    (affineConstraintAngles_contDiff a 0).continuous
  have hs : Function.support f ⊆ anchorIntegrationBox n ρ := by
    intro x hx
    by_contra hn
    apply hx
    dsimp only [f]
    rw [actualLowerCompactAnchorCutoff_affine_zero_off_box hρ hρπ η b δ a i x hn, zero_mul]
  exact hf.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc))

theorem original_lower_anchor_integral_centered_lifts {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (b δ : ℝ) {n : ℕ}
    (i : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) (a : ℝ) :
    (∫ x in angularIntegrationBox n,
      actualLowerAnchorCutoff η b δ ρ i (affineConstraintAngles a x) * F (affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        ∫ x : Fin n → ℝ, actualLowerCompactAnchorCutoff η b δ ρ i
          (centeredConstraintAngles ((2 * Real.pi * l + a) / (n + 1 : ℕ)) x) *
            F (centeredConstraintAngles ((2 * Real.pi * l + a) / (n + 1 : ℕ)) x) := by
  rw [angularIntegrationBox_eq_anchor_integral ρ _ (fun k x => by
    rw [affineConstraintAngles_toroidal_c03, actualLowerAnchorCutoff_toroidal, hF])]
  have hi (l : ℤ) := actual_lower_anchor_compact_integrable hρ hρπ η b δ (2 * Real.pi * l + a) i F hc
  calc
    _ = ∫ x in anchorIntegrationBox n ρ,
        ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
          actualLowerCompactAnchorCutoff η b δ ρ i (affineConstraintAngles (2 * Real.pi * l + a) x) *
            F (affineConstraintAngles (2 * Real.pi * l + a) x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact fun x hx => actual_lower_anchor_finite_periodization hη hρ hρπ hgap b δ i F hF a x hx
    _ = ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        ∫ x in anchorIntegrationBox n ρ,
          actualLowerCompactAnchorCutoff η b δ ρ i (affineConstraintAngles (2 * Real.pi * l + a) x) *
            F (affineConstraintAngles (2 * Real.pi * l + a) x) :=
      integral_finsetSum _ (fun l _ => (hi l).integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [actualLowerCompactAnchorCutoff_affine_zero_off_box hρ hρπ η b δ _ i x hx, zero_mul])]
      exact affineConstraint_integral_centered (2 * Real.pi * l + a)
        (fun θ => actualLowerCompactAnchorCutoff η b δ ρ i θ * F θ)

end IsingBulk.AnisoF002.Isotropic
