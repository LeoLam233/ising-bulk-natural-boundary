import IsingBulk.AnisoF002.C03.IsotropicIntegratedRightCurrent
import IsingBulk.AnisoF002.C03.IsotropicInitialDensityAttachment
import IsingBulk.AnisoF002.C03.IsotropicRadialJetIdentification
import IsingBulk.AnisoF002.C03.IsotropicCompactParticleHolomorphy

/-!
# Actual compact-mean coefficient jets are the full integrated currents

The base integral is attached to the original complete normalized
physical coefficient. The genuine integrated current identities then
identify every complex parameter derivative through a fixed retained
order. Smooth population and compact angular cutoffs are never
continued analytically.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators ContDiff

theorem exists_actual_compact_mean_current_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ (n : ℕ) (R : Finset (Fin (n + 2) × Fin (n + 2))), R ⊆ indexPairs (n + 2) →
      ∀ j : ℕ, j ≤ R.card → ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) η τ ξ b δB ρB μ σ)
          (isotropicRadialParameter α ε) =
        ∫ x : Fin (n + 1) → ℝ,
          actualTransportedDensity σ η τ ξ (actualLowerCompactRightCutoff η b δB ρB (n + 2)) j
            (isotropicRadialParameter α ε, centeredConstraintAngles μ x) := by
  obtain ⟨βI, hβI, hβI1, hcurrent⟩ := exists_actual_integrated_right_current_buffer α b hα hb hpoint
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  obtain ⟨δA, hδA, hattach⟩ := exists_actual_initial_density_attachment (2 * Real.cos α) hS
  let β := min βI δA
  have hβ : 0 < β := lt_min hβI hδA
  have hbI : β ≤ βI := min_le_left _ _
  have hbA : β ≤ δA := min_le_right _ _
  have hβ1 : β ≤ 1 := hbI.trans hβI1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δI, hδI, _, hi⟩ := hcurrent η hη hwidth
  let δ := min β (min δI (δA / 8))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdI : δ ≤ δI := (min_le_right _ _).trans (min_le_left _ _)
  have hdA8 : δ ≤ δA / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hdA : δ ≤ δA := by linarith only [hdA8, hδA]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro δB ρB hcut hδB hρB n R hR j hj σ hσ τ hτ ξ hξ μ ε hε
  let g := actualLowerCompactRightCutoff η b δB ρB (n + 2)
  let f := compactMeanPhysicalCoefficient (n + 1) η τ ξ b δB ρB μ σ
  let I : ℕ → ℝ → ℂ := fun k e => ∫ x : Fin (n + 1) → ℝ,
    actualTransportedDensity σ η τ ξ g k (isotropicRadialParameter α e, centeredConstraintAngles μ x)
  have hg : ContDiff ℝ ∞ g := actualLowerCompactRightCutoff_contDiff η b δB ρB (n + 2)
  obtain ⟨Ag, Cg, hAg, hCg, hgjet⟩ := actualLowerCompactRightCutoff_jets hcut η (j + 1)
  let Lg := Ag * Cg ^ (n + 2) * (n + 2 : ℕ) ^ (2 * (j + 1))
  have hLg : 0 ≤ Lg := by dsimp [Lg]; positivity
  have hgj : FiniteJetControl (j + 1) g Lg := hgjet (n + 2) (by omega)
  have hgsupport : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - β) β := by
    intro θ hθ k
    have hh := compactRightProduct_weighted_tsupport hcut
      (fun y : Fin (n + 2) → ℝ => (lowerPopulationCutoff η y : ℂ)) hθ k
    exact ⟨by linarith [hh.1], hh.2.trans hρB⟩
  have hgsupportI : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - βI) βI := by
    intro θ hθ k
    have hh := hgsupport θ hθ k
    exact ⟨by linarith [hh.1], hh.2.trans hbI⟩
  have hrad (e : ℝ) (he : e ∈ Ioo 0 δ) := isotropicRadialParameter_estimates α e hα he.1 (he.2.le.trans hd1)
  have hbase (e : ℝ) (he : e ∈ Ioo 0 δ) : I 0 e = f (isotropicRadialParameter α e) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      let θ := centeredConstraintAngles μ x
      by_cases hsupp : θ ∈ tsupport g
      · have hsnear : dist (isotropicRadialParameter α e) ((2 * Real.cos α : ℝ) : ℂ) < δA :=
          (hrad e he).2.2.2.2.trans_lt (by linarith only [he.2, hdA8, hδA])
        have hθ : ∀ k, θ k ∈ Icc (-Real.pi - δA) δA := by
          intro k
          have hh := hgsupport θ hsupp k
          exact ⟨by linarith [hh.1, hb.2], hh.2.trans hbA⟩
        exact hattach (n + 2) (by omega) _ (hrad e he).2.2.2.1 hsnear η τ ξ hη
          ⟨hτ.1, hτ.2.trans hdA⟩ hξ θ hθ σ g
      · have hz := (actualTransportedDensity_zero_germ σ η τ ξ g 0
          (isotropicRadialParameter α e, θ) hsupp).eq_of_nhds
        have hgz : g θ = 0 := (notMem_tsupport_iff_eventuallyEq.mp hsupp).eq_of_nhds
        change actualTransportedDensity σ η τ ξ g 0 (isotropicRadialParameter α e, θ) = g θ * _
        rw [hz, hgz, zero_mul]
  have hstep (k : ℕ) (hk : k < j) (e : ℝ) (he : e ∈ Ioo 0 δ) :
      HasDerivAt (I k) (isotropicRadialDerivative α e * I (k + 1) e) e := by
    exact (hi n R hR k (by omega) g Lg hLg hg (hgj.mono_order (by omega)) hgsupportI σ hσ
      τ ⟨hτ.1, hτ.2.trans hdI⟩ ξ hξ μ e ⟨he.1, he.2.trans_le hdI⟩).2.2
  have hid := radial_current_identifies_iteratedDeriv f I (isotropicRadialParameter α)
    (isotropicRadialDerivative α) (Ioo 0 δ) isOpen_Ioo j
    (fun e he => compactMeanPhysicalCoefficient_analyticAt hcut (n + 1) η τ ξ μ σ
      hη hτ.1 hξ.1 hσ _ (hrad e he).2.2.2.1)
    (fun e he => isotropicRadialParameter_hasDerivAt α e he.1)
    (fun e he => isotropicRadialDerivative_ne_zero α e he.1) hbase hstep j le_rfl ε hε
  exact hid.symm

end
end IsingBulk.AnisoF002.Isotropic
