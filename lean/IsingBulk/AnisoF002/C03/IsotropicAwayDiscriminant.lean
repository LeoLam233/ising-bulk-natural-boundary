import IsingBulk.AnisoF002.C03.IsotropicFixedOccupancyCurve

/-!
# Uniform physical phase control away from the right branch

Only the elementary discriminant is continued across the limiting arc.
The actual phase is evaluated on its genuine upper physical sheet.
The compact discriminant margin is uniform over all actual populations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def rightAwayAngles (b R : ℝ) : Set ℝ := Icc (-Real.pi) 0 ∩ {θ | R / 2 ≤ |θ + b|}

def rightAwayParameterSegment (S b R : ℝ) : Set (ℂ × ℂ) :=
  (fun θ : ℝ => ((S : ℂ), (θ : ℂ))) '' rightAwayAngles b R

theorem rightAwayParameterSegment_isCompact (S b R : ℝ) :
    IsCompact (rightAwayParameterSegment S b R) := by
  apply IsCompact.image _ (continuous_const.prodMk Complex.continuous_ofReal)
  exact isCompact_Icc.inter_right (isClosed_le continuous_const ((continuous_id.add_const b).abs))

def isotropicDiscriminant (q : ℂ × ℂ) : ℂ := 1 - isotropicDispersion q ^ 2

theorem isotropicDiscriminant_continuous : Continuous isotropicDiscriminant :=
  continuous_const.sub ((continuous_fst.sub (Complex.continuous_cos.comp continuous_snd)).pow 2)

theorem rightAway_discriminant_ne_zero (S b R θ : ℝ) (hS : 0 < S)
    (hb : b ∈ Icc 0 Real.pi) (hpoint : 1 + Real.cos b = S) (hR : 0 < R)
    (hθ : θ ∈ rightAwayAngles b R) :
    isotropicDiscriminant ((S : ℂ), (θ : ℂ)) ≠ 0 := by
  have hreal : 1 - (S - Real.cos θ) ^ 2 ≠ 0 := by
    intro hz
    have he : (S - Real.cos θ) ^ 2 = (1 : ℝ) ^ 2 := by linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with hpos | hneg
    · have hc : Real.cos (-θ) = Real.cos b := by rw [Real.cos_neg]; linarith only [hpoint, hpos]
      have ht : -θ = b := Real.injOn_cos ⟨by linarith [hθ.1.2], by linarith [hθ.1.1]⟩ hb hc
      have hzθ : θ + b = 0 := by linarith only [ht]
      have hn : R / 2 ≤ |θ + b| := hθ.2
      rw [hzθ, abs_zero] at hn
      linarith only [hn, hR]
    · have hc := Real.cos_le_one θ
      linarith only [hc, hneg, hS]
  have he : isotropicDiscriminant ((S : ℂ), (θ : ℂ)) =
      ((1 - (S - Real.cos θ) ^ 2 : ℝ) : ℂ) := by
    simp only [isotropicDiscriminant, isotropicDispersion, ← Complex.ofReal_cos,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one]
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hreal

theorem exists_right_away_discriminant_tube (S b R : ℝ) (hS : 0 < S)
    (hb : b ∈ Icc 0 Real.pi) (hpoint : 1 + Real.cos b = S) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ q ∈ cthickening r (rightAwayParameterSegment S b R),
        isotropicDiscriminant q ≠ 0 ∧ ‖(isotropicDiscriminant q)⁻¹‖ ≤ C := by
  let K := rightAwayParameterSegment S b R
  have hK := rightAwayParameterSegment_isCompact S b R
  have hinside : K ⊆ {q | isotropicDiscriminant q ≠ 0} := by
    rintro q ⟨θ, hθ, rfl⟩
    exact rightAway_discriminant_ne_zero S b R θ hS hb hpoint hR hθ
  have hopen : IsOpen {q | isotropicDiscriminant q ≠ 0} :=
    isOpen_ne.preimage isotropicDiscriminant_continuous
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hopen hinside
  have hinv : ContinuousOn (fun q => (isotropicDiscriminant q)⁻¹) (cthickening r K) :=
    isotropicDiscriminant_continuous.continuousOn.inv₀ (fun q hq => hsub hq)
  obtain ⟨C, hC⟩ := hK.cthickening.exists_bound_of_continuousOn hinv
  refine ⟨r, max 1 C, hr, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  exact ⟨hsub hq, (hC q hq).trans (le_max_right _ _)⟩

theorem phase_inverse_bound_of_discriminant (W : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ‖(1 - W ^ 2)⁻¹‖ ≤ C) :
    ‖Complex.sin (upperPhysicalPhase W)‖⁻¹ ≤ C + 1 := by
  let x := ‖Complex.sin (upperPhysicalPhase W)‖⁻¹
  have hx : 0 ≤ x := inv_nonneg.mpr (norm_nonneg _)
  have hs : ‖Complex.sin (upperPhysicalPhase W)‖ ^ 2 = ‖1 - W ^ 2‖ := by
    rw [← norm_pow, Complex.sin_sq, upperPhysicalPhase_cos]
  have he : x ^ 2 = ‖(1 - W ^ 2)⁻¹‖ := by dsimp [x]; rw [inv_pow, hs, norm_inv]
  have hsC : x ^ 2 ≤ C := he ▸ hbound
  change x ≤ C + 1
  by_cases hsmall : x ≤ 1
  · linarith only [hsmall, hC]
  · have hlarge : 1 ≤ x := le_of_lt (lt_of_not_ge hsmall)
    have hsq : x ≤ x ^ 2 := by simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hlarge hx
    linarith only [hsq, hsC]

/-- The fixed-population connecting curves have a uniform physical
phase inverse away from the branch, including both endpoint slivers.
No continuation of a wrong boundary root is used. -/
theorem exists_fixedOccupancy_away_phase_bound (S b R : ℝ) (hS : 0 < S)
    (hb : b ∈ Icc 0 Real.pi) (hpoint : 1 + Real.cos b = S) (hR : 0 < R) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ s : ℂ, dist s (S : ℂ) ≤ δ → ∀ η τ ρ υ θ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
        θ ∈ Icc (-Real.pi - δ) δ → R ≤ |θ + b| →
        ‖Complex.sin (upperPhysicalPhase (isotropicDispersion
          (s, fixedOccupancyAngle η τ ρ υ θ)))‖⁻¹ ≤ A := by
  obtain ⟨r, C, hr, hC, hbound⟩ := exists_right_away_discriminant_tube S b R hS hb hpoint hR
  let δ := min 1 (min (r / 4) (R / 4))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hδr : δ ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, C + 1, hδ, min_le_left _ _, by positivity, ?_⟩
  intro s hs η τ ρ υ θ hτ hρ hυ hθ haway
  obtain ⟨a, ha, hdist⟩ := interval_clamp_distance (-Real.pi) 0 δ θ
    (neg_nonpos.mpr Real.pi_pos.le) hδ.le (by simpa only [zero_add] using hθ)
  have haaway : R / 2 ≤ |a + b| := by
    have habs := abs_sub_abs_le_abs_sub (θ + b) (a + b)
    rw [add_sub_add_right_eq_sub] at habs
    linarith only [habs, hdist, haway, hδR, hR]
  have hmem : ((S : ℂ), (a : ℂ)) ∈ rightAwayParameterSegment S b R :=
    ⟨a, ⟨ha, haaway⟩, rfl⟩
  have hangle : dist (fixedOccupancyAngle η τ ρ υ θ) (a : ℂ) ≤ r := by
    calc
      _ ≤ dist (fixedOccupancyAngle η τ ρ υ θ) (θ : ℂ) + dist (θ : ℂ) (a : ℂ) := dist_triangle _ _ _
      _ ≤ τ + δ := add_le_add
        (by simpa only [dist_eq_norm] using fixedOccupancyAngle_displacement η τ ρ υ θ hτ.1 hρ hυ)
        (by simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hdist)
      _ ≤ r := by linarith only [hτ.2, hδr, hr]
  have hq : (s, fixedOccupancyAngle η τ ρ υ θ) ∈ cthickening r (rightAwayParameterSegment S b R) := by
    apply mem_cthickening_of_dist_le _ _ _ _ hmem
    rw [Prod.dist_eq, max_le_iff]
    exact ⟨hs.trans (by linarith only [hδr, hr]), hangle⟩
  exact phase_inverse_bound_of_discriminant _ C hC.le (hbound _ hq).2

end IsingBulk.AnisoF002.Isotropic
