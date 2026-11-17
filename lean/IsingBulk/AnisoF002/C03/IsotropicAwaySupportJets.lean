import IsingBulk.AnisoF002.C03.IsotropicAwaySupportCurrent
import IsingBulk.AnisoF002.C03.IsotropicInitialDensityAttachment
import IsingBulk.AnisoF002.C03.IsotropicRadialJetIdentification
import IsingBulk.AnisoF002.C03.IsotropicCompactWeightedHolomorphy

/-!
# Every physical coefficient derivative away from total coincidence

An arbitrary smooth compact angular cutoff vanishing near constant
tuples is admitted at its actual real strength. There is no retained
pair budget or particle-order restriction in this fixed-particle result.
The complete physical coefficient, determinant and current are literal.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators ContDiff

theorem exists_actual_away_support_coefficient_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ n : ℕ, ∀ g : (Fin (n + 2) → ℝ) → ℂ, ContDiff ℝ ∞ g →
        (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β) →
        (∀ θ ∈ tsupport g, ∃ i l, θ i ≠ θ l) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ μ : ℝ, ∀ j : ℕ, ∀ ε ∈ Ioo 0 δ,
        Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j
          (isotropicRadialParameter α ε, centeredConstraintAngles μ x)) ∧
        iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ g)
          (isotropicRadialParameter α ε) =
          ∫ x : Fin (n + 1) → ℝ, actualTransportedDensity σ η τ ξ g j
            (isotropicRadialParameter α ε, centeredConstraintAngles μ x) := by
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  have hbS : rightBranchEndpoint (2 * Real.cos α) = b := by
    unfold rightBranchEndpoint
    rw [show 2 * Real.cos α - 1 = Real.cos b by linarith only [hpoint]]
    exact Real.arccos_cos hb.1.le hb.2.le
  obtain ⟨βR, hβR, hβR1, hregular⟩ := exists_actual_away_support_regular_current (2 * Real.cos α) hS
  obtain ⟨δA, hδA, hattach⟩ := exists_actual_initial_density_attachment (2 * Real.cos α) hS
  let β := min βR δA
  have hβ : 0 < β := lt_min hβR hδA
  have hbR : β ≤ βR := min_le_left _ _
  have hbA : β ≤ δA := min_le_right _ _
  have hβ1 : β ≤ 1 := hbR.trans hβR1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δR, hδR, _, hr⟩ := hregular η hη
  let δ := min β (min (δR / 8) (δA / 8))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdR8 : δ ≤ δR / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hdA8 : δ ≤ δA / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hdR : δ ≤ δR := by linarith only [hdR8, hδR]
  have hdA : δ ≤ δA := by linarith only [hdA8, hδA]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro n g hg hsupport haway σ hσ τ hτ ξ hξ μ j ε hε
  let f := centeredWeightedPhysicalCoefficient η τ ξ μ σ g
  let I : ℕ → ℝ → ℂ := fun k e => ∫ x : Fin (n + 1) → ℝ,
    actualTransportedDensity σ η τ ξ g k (isotropicRadialParameter α e, centeredConstraintAngles μ x)
  have hsuppR : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - βR) βR := by
    rw [hbS]
    intro θ ht k
    have hh := hsupport θ ht k
    exact ⟨by linarith [hh.1], hh.2.trans hbR⟩
  have hrad (e : ℝ) (he : e ∈ Ioo 0 δ) := isotropicRadialParameter_estimates α e hα he.1 (he.2.le.trans hd1)
  have hreg (e : ℝ) (he : e ∈ Ioo 0 δ) : ∀ k : ℕ, ∀ θ : Fin (n + 2) → ℝ,
      ActualCurrentRegularAt σ η τ ξ g k (isotropicRadialParameter α e, θ) :=
    hr (n + 2) (by omega) g hg hsuppR haway _ (hrad e he).2.2.2.1
      ((hrad e he).2.2.2.2.trans_lt (by linarith only [he.2, hdR8, hδR]))
      τ ⟨hτ.1, hτ.2.trans hdR⟩ ξ hξ σ hσ
  have hstep (k : ℕ) (e : ℝ) (he : e ∈ Ioo 0 δ) :=
    integrated_actual_current_of_global_regular α e η τ ξ μ (-b - β) β σ g k he.1
      (by linarith only [hb.1, hβ]) hsupport (hreg e he)
  have hbase (e : ℝ) (he : e ∈ Ioo 0 δ) : I 0 e = f (isotropicRadialParameter α e) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      let θ := centeredConstraintAngles μ x
      by_cases ht : θ ∈ tsupport g
      · have hθ : ∀ k, θ k ∈ Icc (-Real.pi - δA) δA := by
          intro k
          have hh := hsupport θ ht k
          exact ⟨by linarith [hh.1, hb.2], hh.2.trans hbA⟩
        exact hattach (n + 2) (by omega) _ (hrad e he).2.2.2.1
          ((hrad e he).2.2.2.2.trans_lt (by linarith only [he.2, hdA8, hδA]))
          η τ ξ hη ⟨hτ.1, hτ.2.trans hdA⟩ hξ θ hθ σ g
      · have hz := (actualTransportedDensity_zero_germ σ η τ ξ g 0
          (isotropicRadialParameter α e, θ) ht).eq_of_nhds
        have hgz : g θ = 0 := (notMem_tsupport_iff_eventuallyEq.mp ht).eq_of_nhds
        change actualTransportedDensity σ η τ ξ g 0 (isotropicRadialParameter α e, θ) = g θ * _
        rw [hz, hgz, zero_mul]
  have hsupports : Function.support g ⊆ Icc (fun _ => -b - β) (fun _ => β) := by
    intro θ hθ
    have hh := hsupport θ (subset_closure hθ)
    exact ⟨fun k => (hh k).1, fun k => (hh k).2⟩
  have hid := radial_current_identifies_iteratedDeriv f I (isotropicRadialParameter α)
    (isotropicRadialDerivative α) (Ioo 0 δ) isOpen_Ioo j
    (fun e he => (centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ μ σ hη hτ.1 hξ.1
      hσ g hg.continuous hsupports _ (hrad e he).2.2.2.1).1)
    (fun e he => isotropicRadialParameter_hasDerivAt α e he.1)
    (fun e he => isotropicRadialDerivative_ne_zero α e he.1) hbase
    (fun k _ e he => (hstep k e he).2.2) j le_rfl ε hε
  exact ⟨(hstep j ε hε).1, hid.symm⟩

end
end IsingBulk.AnisoF002.Isotropic
