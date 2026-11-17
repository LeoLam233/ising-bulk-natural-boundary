import IsingBulk.AnisoF002.C03.IsotropicAnchorPeriodization

/-!
# Complete physical anchor coefficients, all jets and named elimination

The original periodic anchor integral equals every compact centered
lift with its full physical density. All ordinary parameter derivatives
are identified. The final chart eliminates the named anchor with an
exact measure-preserving constrained permutation; its ordered cutoff
prefix is evaluated on that same chart, never replaced by a symmetric
substitute.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

theorem actualLowerCompactAnchorCutoff_support_box {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) {N : ℕ} (i : Fin N) :
    Function.support (actualLowerCompactAnchorCutoff η b δ ρ i) ⊆
      Icc (fun _ => -Real.pi - ρ) (fun _ => ρ) :=
  (subset_tsupport _).trans (compactLowerWindowProduct_weighted_tsupport hρ
    (actualLowerAnchorCutoff η b δ ρ i))

theorem actualLowerCompactAnchorCutoff_hasCompactSupport {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) {N : ℕ} (i : Fin N) :
    HasCompactSupport (actualLowerCompactAnchorCutoff η b δ ρ i) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (compactLowerWindowProduct_weighted_tsupport hρ (actualLowerAnchorCutoff η b δ ρ i))

theorem actualLowerCompactAnchorCutoff_jet_cosine_gap {η b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (hbρ : b + δ / 2 + ρ < Real.pi)
    {N : ℕ} (i : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hne : iteratedFDeriv ℝ k (actualLowerCompactAnchorCutoff η b δ ρ i) θ ≠ 0) :
    actualUpperPopulation η θ ≤ 1 / 2 ∧
      (∀ j, θ j ∈ Icc (-Real.pi - ρ) ρ) ∧
      0 < Real.cos b - Real.cos (b + δ / 2) ∧
      Real.cos b - Real.cos (b + δ / 2) ≤ Real.cos b - Real.cos (θ i) := by
  obtain ⟨hP, hrect, hi⟩ := actualLowerCompactAnchorCutoff_jet_support h hη hρπ hgap i k θ hne
  have hg := compact_left_anchor_cosine_gap h.b_pos h.delta_pos h.rho_pos.le hbρ ⟨(hrect i).1, hi⟩
  exact ⟨hP, hrect, hg.1, by linarith only [hg.2]⟩

theorem admissibleAnchorLifts_card_le (N : ℕ) (hN : 0 < N) (ρ a : ℝ)
    (hρπ : ρ < Real.pi / 2) : (admissibleRightLifts N Real.pi ρ a).card ≤ N := by
  apply int_interval_card_le_of_real_width
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (((N : ℝ) * ρ - a) / (2 * Real.pi)) -
      (((N : ℝ) * (-Real.pi - ρ) - a) / (2 * Real.pi)) =
      (N : ℝ) * (Real.pi + 2 * ρ) / (2 * Real.pi) := by ring
  rw [he]
  exact (div_lt_iff₀ (by positivity)).mpr
    (mul_lt_mul_of_pos_left (by linarith only [hρπ]) hNp)

theorem actual_original_anchor_physical_integral_centered_lifts {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (b δ τ ξ a : ℝ)
    (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) {n : ℕ} (i : Fin (n + 1))
    (σ S : ℂ) (hσ : ‖σ‖ ≤ 1) (hS : 0 < S.im) :
    actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a S =
      ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        centeredWeightedPhysicalCoefficient η τ ξ ((2 * Real.pi * l + a) / (n + 1 : ℕ)) σ
          (actualLowerCompactAnchorCutoff η b δ ρ i) S := by
  exact original_lower_anchor_integral_centered_lifts hη hρ hρπ hgap b δ i
    (fun θ => homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, θ))
    (actual_physical_density_continuous (by omega) S σ hS hσ η τ ξ hη hτ hξ)
    (fun k θ => homotopyPulledDensity_toroidal η τ ξ _ (isotropicBarePhysicalDensity_periodic S σ) k θ) a

theorem actual_original_anchor_parameter_jets_centered_lifts {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (b δ τ ξ a : ℝ)
    (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) {n : ℕ} (i : Fin (n + 1))
    (σ S : ℂ) (hσ : ‖σ‖ ≤ 1) (hS : 0 < S.im) (j : ℕ) :
    iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a) S =
      ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ
          ((2 * Real.pi * l + a) / (n + 1 : ℕ)) σ (actualLowerCompactAnchorCutoff η b δ ρ i)) S := by
  have he : actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a =ᶠ[𝓝 S]
      fun T => ∑ l ∈ admissibleRightLifts (n + 1) Real.pi ρ a,
        centeredWeightedPhysicalCoefficient η τ ξ ((2 * Real.pi * l + a) / (n + 1 : ℕ)) σ
          (actualLowerCompactAnchorCutoff η b δ ρ i) T := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hS] with T hT
    exact actual_original_anchor_physical_integral_centered_lifts hη hρ hρπ hgap b δ τ ξ a hτ hξ i σ T hσ hT
  rw [(he.iteratedDeriv j).eq_of_nhds]
  apply iteratedDeriv_fun_sum
  intro l _
  exact (centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ _ σ hη hτ hξ hσ
    (actualLowerCompactAnchorCutoff η b δ ρ i)
    (actualLowerCompactAnchorCutoff_contDiff η b δ ρ i (k := 0)).continuous
    (actualLowerCompactAnchorCutoff_support_box hρ η b δ i) S hS).1.contDiffAt

def namedAnchorAngles {n : ℕ} (i : Fin (n + 1)) (μ : ℝ)
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => centeredConstraintAngles μ x (Equiv.swap i (Fin.last n) k)

theorem namedAnchorAngles_anchor {n : ℕ} (i : Fin (n + 1)) (μ : ℝ) (x : Fin n → ℝ) :
    namedAnchorAngles i μ x i = μ - ∑ j, x j := by
  simp only [namedAnchorAngles, Equiv.swap_apply_left, centeredConstraintAngles,
    NegativeHT.Angular.independentChart_last]
  ring

theorem namedAnchorAngles_independent {n : ℕ} (i : Fin (n + 1)) (μ : ℝ)
    (x : Fin n → ℝ) (j : Fin n) :
    namedAnchorAngles i μ x (Equiv.swap i (Fin.last n) j.castSucc) = μ + x j := by
  simp only [namedAnchorAngles, Equiv.swap_apply_self, centeredConstraintAngles,
    NegativeHT.Angular.independentChart_castSucc]

theorem namedAnchorAngles_integral {n : ℕ} (i : Fin (n + 1)) (μ : ℝ)
    (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ x : Fin n → ℝ, F (namedAnchorAngles i μ x)) =
      ∫ x : Fin n → ℝ, F (centeredConstraintAngles μ x) := by
  have hh := constrainedChartPermutation_integral (Equiv.swap i (Fin.last n))
    (fun x => F (centeredConstraintAngles μ x))
  unfold namedAnchorAngles
  simpa only [centeredConstraintAngles_chartPermutation] using hh

end IsingBulk.AnisoF002.Isotropic
