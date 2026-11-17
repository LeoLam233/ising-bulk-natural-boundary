import IsingBulk.AnisoF002.C03.IsotropicCurrentRegularBuffer
import IsingBulk.AnisoF002.C03.IsotropicRetainedPowerControls
import IsingBulk.AnisoF002.C03.IsotropicInteriorRadialBounds

/-!
# Actual interior data for the integrated complete right current

The angular buffer and deformation radius retain their frozen
quantifier order. At a fixed positive radial parameter, the actual
complete density and its full first real derivative have uniform
bounds on one common parameter neighborhood. The actual flux retains
the positive collision degree needed for its continuous zero value.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators ContDiff

theorem positive_parameter_window (δ ε₀ : ℝ) (hε₀ : 0 < ε₀) (hεδ : ε₀ < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε ∈ ball ε₀ r,
      ε ∈ Icc (ε₀ / 2) ((ε₀ + δ) / 2) ∧ 0 < ε ∧ ε < δ := by
  refine ⟨min (ε₀ / 2) ((δ - ε₀) / 2), by positivity, ?_⟩
  intro ε hε
  rw [mem_ball, Real.dist_eq, abs_sub_lt_iff] at hε
  have h₁ := min_le_left (ε₀ / 2) ((δ - ε₀) / 2)
  have h₂ := min_le_right (ε₀ / 2) ((δ - ε₀) / 2)
  refine ⟨⟨by linarith [hε.2], by linarith [hε.1]⟩, ?_, ?_⟩
  · linarith [hε.2]
  · linarith [hε.1]

theorem exists_actual_interior_current_data (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ j : ℕ, 2 * j + 2 ≤ 2 * R.card →
      ∀ (g : (Fin N → ℝ) → ℂ) (Cg : ℝ), 0 ≤ Cg → ContDiff ℝ ∞ g →
        FiniteJetControl (j + 1) g Cg →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ ε₀ ∈ Ioo 0 δ, ∃ r A C : ℝ, 0 < r ∧ 0 < A ∧ 0 < C ∧
        (∀ ε ∈ ball ε₀ r, ε ∈ Icc (ε₀ / 2) ((ε₀ + δ) / 2) ∧ 0 < ε ∧ ε < δ) ∧
        ∀ ε ∈ ball ε₀ r, ∀ θ : Fin N → ℝ,
          (∀ k, θ k ∈ Icc (-b - β) β) → (∃ i l, θ i ≠ θ l) →
          let q := (isotropicRadialParameter α ε, θ)
          ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) q ∧
          ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g (j + 1)) q ∧
          AnalyticAt ℂ (fun s => actualTransportedDensity σ η τ ξ g j (s, θ)) q.1 ∧
          (∀ k, DifferentiableAt ℝ (actualTransportedFlux σ η τ ξ g j k) q) ∧
          (∀ anchor : Fin N,
            scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection q -
              (∑ k ∈ Finset.univ.erase anchor, scalarPartial (actualTransportedFlux σ η τ ξ g j k)
                (actualAngularDirection k - actualAngularDirection anchor) q) =
              actualTransportedDensity σ η τ ξ g (j + 1) q) ∧
          ‖actualTransportedDensity σ η τ ξ g j q‖ ≤ A ∧
          ‖actualTransportedDensity σ η τ ξ g (j + 1) q‖ ≤ A ∧
          ‖fderiv ℝ (actualTransportedDensity σ η τ ξ g j) q‖ ≤ A ∧
          ∀ t : ℝ, 0 < t → (∀ i l, |θ i - θ l| ≤ 2 * t) → (∃ i l, t ≤ |θ i - θ l|) →
            ∀ k, ‖actualTransportedFlux σ η τ ξ g j k q‖ ≤
              C * (isotropicShellDelta b ε t θ) ^ (2 * R.card - 2 * j - 1) := by
  obtain ⟨βP, hβP, hβP1, hpowers⟩ := exists_actual_retained_power_controls_buffer α b hα hb hpoint
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
  obtain ⟨βR, hβR, _, hregular⟩ := exists_actual_complete_current_regular_buffer (2 * Real.cos α) hS
  obtain ⟨βB, hβB, _, hamplitude⟩ := exists_actual_complete_density_current_buffer (2 * Real.cos α) hS
  let β := min βP (min βR βB)
  have hβ : 0 < β := lt_min hβP (lt_min hβR hβB)
  have hbP : β ≤ βP := min_le_left _ _
  have hbR : β ≤ βR := (min_le_right _ _).trans (min_le_left _ _)
  have hbB : β ≤ βB := (min_le_right _ _).trans (min_le_right _ _)
  have hβ1 : β ≤ 1 := hbP.trans hβP1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δP, hδP, _, hp⟩ := hpowers η hη hwidth
  obtain ⟨δR, hδR, _, hr⟩ := hregular η hη
  obtain ⟨δB, hδB, _, hb'⟩ := hamplitude η hη
  let δ := min β (min δP (min (δR / 8) (δB / 8)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdP : δ ≤ δP := (min_le_right _ _).trans (min_le_left _ _)
  have hdR8 : δ ≤ δR / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdB8 : δ ≤ δB / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdR : δ ≤ δR := by linarith only [hdR8, hδR]
  have hdB : δ ≤ δB := by linarith only [hdB8, hδB]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN R hR j hj g Cg hCg hg hgj σ hσ τ hτ ξ hξ ε₀ hε₀
  obtain ⟨A₀, V, hA₀, hV, hpower⟩ := hp N hN R hR j hj
  obtain ⟨r, hrpos, hwindow⟩ := positive_parameter_window δ ε₀ hε₀.1 hε₀.2
  obtain ⟨M, hM, hmult⟩ := compact_radial_multiplier_first_jets hN α hα σ hσ η τ ξ hη hτ.1 hξ.1
    (ε₀ / 2) ((ε₀ + δ) / 2) (-b - β) β (half_pos hε₀.1) (by linarith [hε₀.2])
  let d := 2 * R.card - 2 * j
  have hd : 2 ≤ d := by dsimp [d]; omega
  let D := Real.sqrt (Real.pi + 2)
  let B₀ := M * A₀ * Cg * (max 1 D) ^ d
  let B₁ := M * (A₀ * (1 + M) * Cg + A₀ * Cg * D) * (max 1 D) ^ d
  let A := max 1 (max B₀ B₁)
  let C := max 1 (V * M * (A₀ * Cg))
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hB₀ : B₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hB₁ : B₁ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hC₀ : V * M * (A₀ * Cg) ≤ C := le_max_right _ _
  refine ⟨r, A, C, hrpos, hA, hC, hwindow, ?_⟩
  intro ε hε θ hθ hne
  dsimp only
  obtain ⟨hewin, hepos, heδ⟩ := hwindow ε hε
  have hrad := isotropicRadialParameter_estimates α ε hα hepos (heδ.le.trans hd1)
  have hsR : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δR :=
    hrad.2.2.2.2.trans_lt (by linarith only [heδ, hdR8, hδR])
  have hsB : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δB :=
    hrad.2.2.2.2.trans_lt (by linarith only [heδ, hdB8, hδB])
  have hθP : ∀ k, θ k ∈ Icc (-b - βP) βP :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbP⟩
  have hθR : ∀ k, θ k ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - βR) βR := by
    rw [hbS]
    exact fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbR⟩
  have hθB : ∀ k, θ k ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - βB) βB := by
    rw [hbS]
    exact fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbB⟩
  obtain ⟨i, l, hil⟩ := hne
  obtain ⟨hds, hda, hfs, hcur⟩ := hr N hN _ hrad.2.2.2.1 hsR τ ⟨hτ.1, hτ.2.trans hdR⟩ ξ hξ θ
    hθR i l hil σ hσ g hg j
  have hnextsmooth := (hr N hN _ hrad.2.2.2.1 hsR τ ⟨hτ.1, hτ.2.trans hdR⟩ ξ hξ θ
    hθR i l hil σ hσ g hg (j + 1)).1
  have hcut : ContDiffAt ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => g q.2)
      (isotropicRadialParameter α ε, θ) := hg.contDiffAt.comp _ contDiffAt_snd
  let anchor : Fin N := ⟨0, hN⟩
  have hbs := (hb' N hN _ hrad.2.2.2.1 hsB τ ⟨hτ.1, hτ.2.trans hdB⟩ ξ hξ θ hθB
    i l hil anchor σ hσ (fun q => g q.2) hcut j).1
  obtain ⟨hm, hdm, hmap⟩ := hmult ε hewin θ hθ
  have hms := (actualTransportDensityMultiplier_interior_smooth hN σ hσ η τ ξ hη hτ.1 hξ.1
    (isotropicRadialParameter α ε, θ) hrad.2.2.2.1).differentiableAt (by simp)
  have hbound (t : ℝ) (ht : 0 < t) (hdiam : ∀ k l, |θ k - θ l| ≤ 2 * t)
      (hlow : ∃ k l, t ≤ |θ k - θ l|) := hpower g Cg hCg hg hgj ε hepos
        (heδ.le.trans hdP) τ ξ ⟨hτ.1, hτ.2.trans hdP⟩ hξ θ hθP t ht hdiam hlow
  obtain ⟨t, ht, hdiam, hlow, _⟩ := exists_actual_diameter_witness hN θ ⟨i, l, hil⟩ 0
  obtain ⟨hΔD, hv₀, hv₁, hv₂, hv₃⟩ := hbound t ht hdiam hlow
  have hΔ := isotropicShellDelta_pos b ε t θ hepos ht
  have hv₂' : ‖fderiv ℝ (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) (isotropicRadialParameter α ε, θ)‖ ≤
      A₀ * (1 + M) * Cg * (isotropicShellDelta b ε t θ) ^ (d - 1) := by
    apply hv₂.trans
    gcongr
  obtain ⟨hv, hn, hdens, _⟩ := actual_retained_density_local_bounds σ η τ ξ g j
    (isotropicRadialParameter α ε, θ) A₀ V M Cg (isotropicShellDelta b ε t θ) D d hA₀.le hV.le
    (zero_le_one.trans hM) hCg hΔ hΔD hd hv₀ hv₁ hv₂' hv₃ hm hdm
    (hbs.differentiableAt (by simp)) hms
  refine ⟨hds, hnextsmooth, hda, hfs, hcur, hv.trans hB₀, hn.trans hB₀, hdens.trans hB₁, ?_⟩
  intro t ht hdia hlo k
  obtain ⟨_, hv₀, _, _, hv₃⟩ := hbound t ht hdia hlo
  have hh := actualTransportedFlux_retained_bound σ η τ ξ g j k
    (isotropicRadialParameter α ε, θ) (A₀ * Cg) V M (isotropicShellDelta b ε t θ) d
    (by positivity) hV.le (zero_le_one.trans hM) (isotropicShellDelta_pos b ε t θ hepos ht)
    (by omega) hv₀ (hv₃ k) hm
  exact hh.trans (mul_le_mul_of_nonneg_right hC₀
    (pow_nonneg (isotropicShellDelta_pos b ε t θ hepos ht).le _))

end
end IsingBulk.AnisoF002.Isotropic
