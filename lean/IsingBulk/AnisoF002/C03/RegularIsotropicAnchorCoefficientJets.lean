import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorIntegratedCurrent
import IsingBulk.AnisoF002.C03.IsotropicCompactWeightedHolomorphy
import IsingBulk.AnisoF002.C03.IsotropicRadialJetIdentification

/-!
# Every actual compact anchored coefficient jet is its full current integral

The base is the original normalized physical density. Ordinary complex
parameter derivatives are identified from the actual integrated radial
current and the independent holomorphy of the original weighted integral.
There is no retained-particle restriction or coincidence exclusion.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter Metric MeasureTheory

theorem exists_actual_anchored_coefficient_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ n : ℕ, ∀ a : Fin (n + 2), ∀ g : (Fin (n + 2) → ℝ) → ℂ,
      ContDiff ℝ ∞ g → (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-Real.pi - β) β) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ μ : ℝ, ∀ j : ℕ, ∀ ε ∈ Ioo 0 δ,
        Integrable (fun x : Fin (n + 1) → ℝ => anchoredTransportedDensity a σ η τ ξ g j
          (isotropicRadialParameter α ε, centeredConstraintAngles μ x)) ∧
        iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ g)
          (isotropicRadialParameter α ε) =
          ∫ x : Fin (n + 1) → ℝ, anchoredTransportedDensity a σ η τ ξ g j
            (isotropicRadialParameter α ε, centeredConstraintAngles μ x) := by
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  obtain ⟨βC, hβC, hβC1, hcurrent⟩ := exists_actual_anchored_current_buffer (2 * Real.cos α) hS
  obtain ⟨δU, hδU, hinverse⟩ := exists_actual_oneSided_inverse_data (2 * Real.cos α) hS
  let β := min βC (δU / 2)
  have hβ : 0 < β := lt_min hβC (half_pos hδU)
  have hbC : β ≤ βC := min_le_left _ _
  have hbU : β < δU := (min_le_right _ _).trans_lt (half_lt_self hδU)
  have hβ1 : β ≤ 1 := hbC.trans hβC1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δC, hδC, _, hc⟩ := hcurrent η hη
  let δ := min β (min (δC / 8) (δU / 8))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdC8 : δ ≤ δC / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hdU8 : δ ≤ δU / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hdC : δ ≤ δC := by linarith only [hdC8, hδC]
  have hdU : δ ≤ δU := by linarith only [hdU8, hδU]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro n a g hg hsupport σ hσ τ ξ hτ hξ μ j ε hε
  let f := centeredWeightedPhysicalCoefficient η τ ξ μ σ g
  let I : ℕ → ℝ → ℂ := fun k e => ∫ x : Fin (n + 1) → ℝ,
    anchoredTransportedDensity a σ η τ ξ g k (isotropicRadialParameter α e, centeredConstraintAngles μ x)
  have hsuppC : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-Real.pi - βC) βC := by
    intro θ hθ i
    have hi := hsupport θ hθ i
    exact ⟨by linarith only [hi.1, hbC], hi.2.trans hbC⟩
  have hrad (e : ℝ) (he : e ∈ Ioo 0 δ) := isotropicRadialParameter_estimates α e hα he.1 (he.2.le.trans hd1)
  have hreg (e : ℝ) (he : e ∈ Ioo 0 δ) (k : ℕ) (θ : Fin (n + 2) → ℝ) :
      AnchoredCurrentState a σ η τ ξ g k (isotropicRadialParameter α e, θ) := by
    have hsnear : dist (isotropicRadialParameter α e) ((2 * Real.cos α : ℝ) : ℂ) < δC :=
      (hrad e he).2.2.2.2.trans_lt (by linarith only [he.2, hdC8, hδC])
    exact hc (n + 2) (by omega) a σ hσ g hg hsuppC τ ξ
      ⟨hτ.1, hτ.2.trans hdC⟩ hξ _ (hrad e he).2.2.2.1 hsnear θ k
  have hbase (e : ℝ) (he : e ∈ Ioo 0 δ) : I 0 e = f (isotropicRadialParameter α e) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      let θ := centeredConstraintAngles μ x
      by_cases hsupp : θ ∈ tsupport g
      · have hsnear : dist (isotropicRadialParameter α e) ((2 * Real.cos α : ℝ) : ℂ) < δU :=
          (hrad e he).2.2.2.2.trans_lt (by linarith only [he.2, hdU8, hδU])
        have hu := hinverse (n + 2) (by omega) _ (hrad e he).2.2.2.1 hsnear η τ ξ hη
          ⟨hτ.1, hτ.2.trans hdU⟩ hξ θ (fun i =>
            ⟨by linarith only [(hsupport θ hsupp i).1, hbU], (hsupport θ hsupp i).2.trans hbU.le⟩)
        have hsheet (i : Fin (n + 2)) := actual_balanced_homotopy_sheet _ (hrad e he).2.2.2.1
          η τ ξ hη hτ.1 hξ.1 θ i
        have hD (i : Fin (n + 2)) : Complex.sin (actualPhysicalPhase η τ ξ (isotropicRadialParameter α e, θ) i) -
            Complex.sin (actualHomotopyAngle η τ ξ θ i) ≠ 0 := by
          have hd := (hu i).2.2.1
          unfold explicitRightDenominator at hd
          rw [(hu i).2.2.2] at hd
          simpa only [actualPhysicalCoordinate, physicalRegularCoordinate, add_sub_cancel_left,
            actualPhysicalPhase] using hd
        simpa only [homotopyPulledDensity_actual, mul_assoc] using
          anchoredTransportedDensity_zero_physical a σ η τ ξ g (isotropicRadialParameter α e, θ)
            hsheet (fun i => (hu i).2.2.2) hD
      · have hz := (anchoredTransportedDensity_zero_germ a σ η τ ξ g 0
          (isotropicRadialParameter α e, θ) hsupp).eq_of_nhds
        have hgz : g θ = 0 := (notMem_tsupport_iff_eventuallyEq.mp hsupp).eq_of_nhds
        change anchoredTransportedDensity a σ η τ ξ g 0 (isotropicRadialParameter α e, θ) = g θ * _
        rw [hz, hgz, zero_mul]
  have hstep (k : ℕ) (_hk : k < j) (e : ℝ) (he : e ∈ Ioo 0 δ) :
      HasDerivAt (I k) (isotropicRadialDerivative α e * I (k + 1) e) e :=
    (integrated_actual_anchored_current_of_global_regular a α e η τ ξ μ (-Real.pi - β) β σ g k
      he.1 (by linarith [Real.pi_pos]) hsupport (hreg e he)).2.2
  have hgsupp : Function.support g ⊆ Icc (fun _ => -Real.pi - β) (fun _ => β) := by
    intro θ hθ
    exact ⟨fun i => (hsupport θ (subset_closure hθ) i).1,
      fun i => (hsupport θ (subset_closure hθ) i).2⟩
  have hid := radial_current_identifies_iteratedDeriv f I (isotropicRadialParameter α)
    (isotropicRadialDerivative α) (Ioo 0 δ) isOpen_Ioo j
    (fun e he => (centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ μ σ hη hτ.1 hξ.1 hσ
      g hg.continuous hgsupp _ (hrad e he).2.2.2.1).1)
    (fun e he => isotropicRadialParameter_hasDerivAt α e he.1)
    (fun e he => isotropicRadialDerivative_ne_zero α e he.1) hbase hstep j le_rfl ε hε
  exact ⟨(integrated_actual_anchored_current_of_global_regular a α ε η τ ξ μ (-Real.pi - β) β σ g j
    hε.1 (by linarith [Real.pi_pos]) hsupport (hreg ε hε)).1, hid.symm⟩

end IsingBulk.AnisoF002.Isotropic
