import IsingBulk.AnisoF002.C03.IsotropicFixedPhaseNeighborhood

/-!
# Uniform true fixed-population curvature on the full positive right side

The singular branch window and the compact regular remainder are joined
on one common neighborhood. The actual two population fractions remain
arbitrary in [0,1], and the enlarged right endpoint is included.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem exists_fixedOccupancy_positive_phase_curvature (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-b) δ,
        c / Real.sqrt (θ + b + ε + τ * ρ) ^ 3 ≤
          (frozenObliqueRotation * fixedOccupancyPhaseCurvature
            (isotropicRadialParameter α ε) η τ ρ υ θ).re := by
  obtain ⟨rB, cB, hrB, _, hcB, hbranch⟩ := exists_isotropic_positive_branch_curvature α b hα hb hpoint
  let R := min rB (min (η / 2) (b / 2))
  have hR : 0 < R := lt_min hrB (lt_min (half_pos hη) (half_pos hb.1))
  have hRB : R ≤ rB := min_le_left _ _
  have hRη : R < η := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hη)
  have hRb : R ≤ b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hpoint, hcos]
  obtain ⟨rA, cA, hrA, hcA, haway⟩ := exists_fixedPhase_regular_curvature_tube
    (2 * Real.cos α) b R η hS hb hpoint hR
  let δ := min 1 (min rB (rA / 8))
  let c := min cB (cA * Real.sqrt R ^ 3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ rA / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, c, hδ, hδ1, by dsimp [c]; positivity, ?_⟩
  intro ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  have hdepth : 0 ≤ τ * ρ := mul_nonneg hτ.1 hρ.1
  have hdepthle : τ * ρ ≤ δ :=
    ((mul_le_mul_of_nonneg_left hρ.2 hτ.1).trans_eq (mul_one _)).trans hτ.2
  have hu : 0 ≤ θ + b := by linarith only [hθ.1]
  have hT : 0 < θ + b + ε + τ * ρ := by linarith only [hu, hε, hdepth]
  have hsT : 0 < Real.sqrt (θ + b + ε + τ * ρ) := Real.sqrt_pos.mpr hT
  by_cases hlocal : θ + b ≤ R
  · have huabs : |θ + b| < η := by rw [abs_of_nonneg hu]; exact hlocal.trans_lt hRη
    have he := fixedOccupancyPhaseCurvature_on_branch (isotropicRadialParameter α ε)
      b η τ ρ υ (θ + b) hη hwidth huabs
    rw [show -b + (θ + b) = θ by ring] at he
    rw [he]
    apply (div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg (Real.sqrt_nonneg _) 3)).trans
    simpa only [show -b + (θ + b) = θ by ring] using
      hbranch ε hε (hεδ.trans hδB) (θ + b) (τ * ρ)
        ⟨hu, hlocal.trans hRB⟩ ⟨hdepth, hdepthle.trans hδB⟩
  · have hfar : R ≤ θ + b := (lt_of_not_ge hlocal).le
    obtain ⟨v, hv, hdv⟩ := interval_clamp_distance (-b + R / 2) 0 δ θ
      (by linarith only [hRb, hb.1]) hδ.le
      ⟨by linarith only [hfar, hR, hδ], by simpa only [zero_add] using hθ.2⟩
    let q : FixedPhaseParameters := (isotropicRadialParameter α ε, τ, ρ, υ, θ)
    let q₀ : FixedPhaseParameters := (((2 * Real.cos α : ℝ) : ℂ), 0, ρ, υ, v)
    have hq₀ : q₀ ∈ fixedPhaseRegularCompact (2 * Real.cos α) b R := by
      exact ⟨rfl, rfl, hρ, hυ, hv⟩
    have hdist : dist q q₀ ≤ rA := by
      have hs := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.2
      have hsA : dist (isotropicRadialParameter α ε) (((2 * Real.cos α : ℝ) : ℂ)) ≤ rA :=
        hs.trans (by linarith only [hεδ, hδA, hrA])
      have htA : dist τ (0 : ℝ) ≤ rA := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
        linarith only [hτ.2, hδA, hrA]
      have hvA : dist θ v ≤ rA := by
        rw [Real.dist_eq]
        exact hdv.trans (by linarith only [hδA, hrA])
      simpa only [q, q₀, Prod.dist_eq, max_le_iff, dist_self] using
        And.intro hsA (And.intro htA (And.intro hrA.le (And.intro hrA.le hvA)))
    have hq : q ∈ cthickening rA (fixedPhaseRegularCompact (2 * Real.cos α) b R) :=
      mem_cthickening_of_dist_le q q₀ rA _ hq₀ hdist
    have hcurv := (haway q hq).2
    change cA ≤ (frozenObliqueRotation * fixedOccupancyPhaseCurvature
      (isotropicRadialParameter α ε) η τ ρ υ θ).re at hcurv
    apply le_trans _ hcurv
    apply (div_le_iff₀ (pow_pos hsT 3)).mpr
    have hroot : Real.sqrt R ≤ Real.sqrt (θ + b + ε + τ * ρ) :=
      Real.sqrt_le_sqrt (by linarith only [hfar, hε, hdepth])
    exact (min_le_right _ _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg R) hroot 3) hcA.le)

end IsingBulk.AnisoF002.Isotropic
