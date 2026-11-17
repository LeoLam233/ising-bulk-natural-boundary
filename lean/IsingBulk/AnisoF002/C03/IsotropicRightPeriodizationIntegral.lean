import IsingBulk.AnisoF002.C03.IsotropicRightPeriodization

/-!
# Exact compact-lift integrals of the full actual periodic right density

The finite periodization uses the original independent Lebesgue measure.
Every compact lift is integrable, and centering is a translation with
Jacobian one. The complete factorial/angular-normalized physical density
and the actual population cutoff are retained in the final identity.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

/-- The compact lift vanishes outside the unchanged independent box. -/
theorem compactRightProduct_affine_zero_off_box {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (hx : x ∉ regularAngularBox n) :
    compactRightProduct b δ ρ (n + 1) (affineConstraintAngles a x) = 0 := by
  by_contra hn
  have ht := compactRightProduct_weighted_tsupport h (fun _ : (Fin (n + 1) → ℝ) => (1 : ℂ))
    (subset_closure (show (1 : ℂ) * compactRightProduct b δ ρ (n + 1)
      (affineConstraintAngles a x) ≠ 0 by simpa only [one_mul] using hn))
  apply hx
  constructor
  · intro i
    have hh := (ht i.castSucc).1
    simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc] at hh
    linarith only [hh, h.left_gap]
  · intro i
    have hh := (ht i.castSucc).2
    simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc] at hh
    exact hh.trans h.right_gap.le

/-- Every compact lift of a continuous complete density is genuinely
integrable on the full independent-coordinate space. -/
theorem compactRightProduct_affine_integrable {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {n : ℕ} (a : ℝ) (F : (Fin (n + 1) → ℝ) → ℂ) (hF : Continuous F) :
    Integrable (fun x : Fin n → ℝ => compactRightProduct b δ ρ (n + 1) (affineConstraintAngles a x) *
      F (affineConstraintAngles a x)) volume := by
  let f : (Fin n → ℝ) → ℂ := fun x => compactRightProduct b δ ρ (n + 1) (affineConstraintAngles a x) *
    F (affineConstraintAngles a x)
  have hc : Continuous f := ((compactRightProduct_contDiff b δ ρ (n + 1) (k := 0)).continuous.comp
    ((affineConstraintAngles_contDiff a 0).continuous)).mul
    (hF.comp (affineConstraintAngles_contDiff a 0).continuous)
  have hs : Function.support f ⊆ regularAngularBox n := by
    intro x hx
    by_contra hh
    apply hx
    change compactRightProduct b δ ρ (n + 1) (affineConstraintAngles a x) * _ = 0
    rw [compactRightProduct_affine_zero_off_box h a x hh, zero_mul]
  have hcompact : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  exact hc.integrable_of_hasCompactSupport hcompact

/-- The exact full right integral is a finite sum over all admissible
integer means, with no boundary or normalization loss. -/
theorem rightProduct_integral_finite_periodization {b δ ρ β : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β) {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) (a : ℝ) :
    (∫ x in regularAngularBox n,
      rightCutoffProduct b δ ρ (n + 1) (affineConstraintAngles a x) * F (affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x : Fin n → ℝ,
          compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l + a) x) *
            F (affineConstraintAngles (2 * Real.pi * l + a) x) := by
  have hi (l : ℤ) := compactRightProduct_affine_integrable h (2 * Real.pi * l + a) F hc
  calc
    _ = ∫ x in regularAngularBox n,
        ∑ l ∈ admissibleRightLifts (n + 1) b β a,
          compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l + a) x) *
            F (affineConstraintAngles (2 * Real.pi * l + a) x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact fun x hx => rightProduct_finite_periodization h hδ hρ F hF a x hx
    _ = ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x in regularAngularBox n,
          compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l + a) x) *
            F (affineConstraintAngles (2 * Real.pi * l + a) x) :=
      integral_finsetSum _ (fun l _ => (hi l).integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [compactRightProduct_affine_zero_off_box h _ x hx, zero_mul]

theorem affineConstraintAngles_centered_translate {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    affineConstraintAngles a (x + fun _ => a / (n + 1 : ℕ)) =
      centeredConstraintAngles (a / (n + 1 : ℕ)) x := by
  rw [affineConstraintAngles_eq_snoc, centeredConstraintAngles_eq_snoc]
  have hm : ((n + 1 : ℕ) : ℝ) * (a / (n + 1 : ℕ)) = a := by field_simp
  have he : (fun i => a / (n + 1 : ℕ) + x i) = x + fun _ => a / (n + 1 : ℕ) := by
    funext i
    simp only [Pi.add_apply, add_comm]
  rw [he]
  congr 1
  push_cast at hm ⊢
  rw [hm]

theorem affineConstraint_integral_centered {n : ℕ} (a : ℝ) (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ x : Fin n → ℝ, F (affineConstraintAngles a x)) =
      ∫ x : Fin n → ℝ, F (centeredConstraintAngles (a / (n + 1 : ℕ)) x) := by
  have hh := integral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
    (fun x => F (affineConstraintAngles a x)) (fun _ => a / (n + 1 : ℕ))
  rw [← hh]
  simp_rw [affineConstraintAngles_centered_translate]

theorem rightProduct_integral_centered_lifts {b δ ρ β : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β) {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) (a : ℝ) :
    (∫ x in regularAngularBox n,
      rightCutoffProduct b δ ρ (n + 1) (affineConstraintAngles a x) * F (affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x : Fin n → ℝ,
          compactRightProduct b δ ρ (n + 1)
            (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) *
          F (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) := by
  rw [rightProduct_integral_finite_periodization h hδ hρ F hc hF a]
  apply Finset.sum_congr rfl
  intro l _
  simpa only [constrainedRightMean, add_sub_cancel_left] using
    affineConstraint_integral_centered (2 * Real.pi * l + a)
      (fun θ => compactRightProduct b δ ρ (n + 1) θ * F θ)

/-- The physical population weight is periodic under every complete
integer angular translation. -/
theorem lowerPopulationCutoff_toroidal {N : ℕ} (η : ℝ) (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    lowerPopulationCutoff η (toroidalTranslation k θ) = lowerPopulationCutoff η θ := by
  obtain ⟨hp, hm, _, _⟩ := actual_bumps_toroidal η k θ
  unfold lowerPopulationCutoff actualUpperPopulation actualLowerPopulation
  rw [hp, hm]

/-- The genuine fully normalized physical density enters the compact
mean decomposition with the actual lower-population cutoff unchanged. -/
theorem actual_right_density_integral_centered_lifts {b δ ρ β : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β)
    {n : ℕ} (s σ : ℂ) (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (a : ℝ) :
    (∫ x in regularAngularBox n,
      actualLowerRightCutoff η b δ ρ (n + 1) (affineConstraintAngles a x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x : Fin n → ℝ,
          actualLowerCompactRightCutoff η b δ ρ (n + 1)
            (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) *
          homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ)
            (ξ, centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) := by
  let D : (Fin (n + 1) → ℝ) → ℂ :=
    fun θ => homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)
  have hD : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (homotopyPulledDensity_contDiffAt η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)
      (isotropicBarePhysicalDensity_analyticAt (by omega) s σ hσ _
        (fun i => actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i))).continuousAt.comp
          (continuous_const.prodMk continuous_id).continuousAt
  let F : (Fin (n + 1) → ℝ) → ℂ := fun θ => (lowerPopulationCutoff η θ : ℂ) * D θ
  have hFcont : Continuous F := (lowerPopulationCutoff_complex_contDiff η (n + 1) (k := 0)).continuous.mul hD
  have hFper : ∀ k θ, F (toroidalTranslation k θ) = F θ := by
    intro k θ
    dsimp only [F, D]
    rw [lowerPopulationCutoff_toroidal, homotopyPulledDensity_toroidal η τ ξ _
      (isotropicBarePhysicalDensity_periodic s σ)]
  simpa only [F, D, actualLowerRightCutoff, actualLowerCompactRightCutoff, mul_assoc, mul_left_comm] using
    rightProduct_integral_centered_lifts h hδ hρ F hFcont hFper a

end IsingBulk.AnisoF002.Isotropic
