import IsingBulk.AnisoF002.C03.IsotropicFixedPhaseNeighborhood
import IsingBulk.AnisoF002.C03.IsotropicUniformBumpWindow

/-!
# The positive coarea curvature on an angular buffer fixed before η

The real compact curvature interval includes a fixed positive endpoint.
The smooth population transition affects only the later temperature and
homotopy neighborhood; it does not choose the angular support width.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set Metric Filter

theorem physical_positive_buffer_curvature (S b θ : ℝ)
    (hS : 0 < S) (hb : 0 < b ∧ b < Real.pi) (hpoint : 1 + Real.cos b = S)
    (hθ : -b < θ ∧ θ < b) :
    isotropicDiscriminant ((S : ℂ), (θ : ℂ)) ∈ Complex.slitPlane ∧
      0 < (frozenObliqueRotation * physicalPhaseNegativeCurvature (S : ℂ) (θ : ℂ)).re := by
  by_cases hn : θ ≤ 0
  · exact physical_positive_right_curvature S b θ hS hb hpoint ⟨hθ.1, hn⟩
  · have hh := physical_positive_right_curvature S b (-θ) hS hb hpoint
      ⟨by linarith only [hθ.2], by linarith only [hn]⟩
    simpa only [isotropicDiscriminant, isotropicDispersion, physicalPhaseNegativeCurvature_sqrt,
      Complex.ofReal_neg, Complex.cos_neg] using hh

def fixedPhaseBufferCompact (S b R β : ℝ) : Set FixedPhaseParameters :=
  {(S : ℂ)} ×ˢ ({(0 : ℝ)} ×ˢ (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc (-b + R / 2) β)))

theorem fixedPhaseBufferCompact_isCompact (S b R β : ℝ) :
    IsCompact (fixedPhaseBufferCompact S b R β) :=
  isCompact_singleton.prod (isCompact_singleton.prod
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))

theorem exists_fixedPhase_buffer_curvature_tube (S b R β η : ℝ)
    (hS : 0 < S) (hb : 0 < b ∧ b < Real.pi) (hpoint : 1 + Real.cos b = S)
    (hR : 0 < R) (hβ : β < b) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ q ∈ cthickening δ (fixedPhaseBufferCompact S b R β),
        isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧
          c ≤ (frozenObliqueRotation * fixedPhaseCurvatureParameters η q).re := by
  let K := fixedPhaseBufferCompact S b R β
  let H : FixedPhaseParameters → ℝ := fun q => (frozenObliqueRotation * fixedPhaseCurvatureParameters η q).re
  have hK := fixedPhaseBufferCompact_isCompact S b R β
  have hregular : ∀ q ∈ K,
      isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧ 0 < H q := by
    rintro ⟨s, τ, ρ, υ, θ⟩ ⟨hs, hτ, _, _, hθ⟩
    have hs' : s = (S : ℂ) := hs
    have hτ' : τ = 0 := hτ
    subst s τ
    have hh := physical_positive_buffer_curvature S b θ hS hb hpoint
      ⟨by linarith only [hθ.1, hR], hθ.2.trans_lt hβ⟩
    simpa only [H, (fixedPhase_zero_values η (S : ℂ) ρ υ θ).1,
      (fixedPhase_zero_values η (S : ℂ) ρ υ θ).2] using hh
  have hHcont (q : FixedPhaseParameters)
      (hq : isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane) :
      ContinuousAt H q :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul (fixedPhaseCurvatureParameters_continuousAt η q hq))
  obtain ⟨c, hc, hclower⟩ := hK.exists_forall_le'
    (fun q hq => (hHcont q (hregular q hq).1).continuousWithinAt)
    (fun q hq => (hregular q hq).2)
  let O : Set FixedPhaseParameters :=
    {q | isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧ c / 2 < H q}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hd := (isotropicDiscriminant_continuous.comp (fixedPhasePoint_continuous η)).continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds hq.1)
    have hp := (hHcont q hq.1).eventually (lt_mem_nhds hq.2)
    filter_upwards [hd, hp] with p hdp hpp
    exact ⟨hdp, hpp⟩
  have hsub : K ⊆ O := fun q hq =>
    ⟨(hregular q hq).1, lt_of_lt_of_le (by linarith only [hc]) (hclower q hq)⟩
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open hO hsub
  exact ⟨δ, c / 2, hδ, half_pos hc, fun q hq => ⟨(hδsub hq).1, (hδsub hq).2.le⟩⟩

theorem fixedOccupancyPhaseCurvature_geometric_branch (s : ℂ) (b η τ ρ υ u : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < Real.sin b / 2) :
    fixedOccupancyPhaseCurvature s η τ ρ υ (-b + u) =
      physicalPhaseNegativeCurvature s (((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ)) := by
  obtain ⟨hp, hm⟩ := lower_branch_plateau_geometric_derivatives b η u hη hwidth hu
  have hnear : ∀ᶠ x in 𝓝 (-b + u), |x + b| < Real.sin b / 2 := by
    have hc : ContinuousAt (fun x : ℝ => |x + b|) (-b + u) := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [show -b + u + b = u by ring] using hu))
  have hpd : deriv (upperPeriodicBump η) =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_geometric_derivatives b η (x + b) hη hwidth hx).1
    rwa [show -b + (x + b) = x by ring] at hh
  have hmd : deriv (lowerPeriodicBump η) =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_geometric_derivatives b η (x + b) hη hwidth hx).2
    rwa [show -b + (x + b) = x by ring] at hh
  have hp2 : deriv (deriv (upperPeriodicBump η)) (-b + u) = 0 := by
    simpa only [deriv_const] using hpd.deriv_eq
  have hm2 : deriv (deriv (lowerPeriodicBump η)) (-b + u) = 0 := by
    simpa only [deriv_const] using hmd.deriv_eq
  simp only [fixedOccupancyPhaseCurvature, fixedOccupancySlope, fixedOccupancySecondSlope,
    hp, hm, hp2, hm2, mul_zero, sub_zero, Complex.ofReal_zero, one_pow, mul_one]
  rw [fixedOccupancyAngle_geometric_branch b η τ ρ υ u hη hwidth hu.le]

/-- The angular width β is fixed before η. The later δ controls only
radial depth and homotopy time, on the entire already fixed right arc. -/
theorem exists_fixedOccupancy_positive_curvature_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ c : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-b) β,
        c / Real.sqrt (θ + b + ε + τ * ρ) ^ 3 ≤
          (frozenObliqueRotation * fixedOccupancyPhaseCurvature
            (isotropicRadialParameter α ε) η τ ρ υ θ).re := by
  let β := min 1 (b / 4)
  have hβ : 0 < β := lt_min zero_lt_one (div_pos hb.1 (by norm_num))
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβb : β < b := (min_le_right _ _).trans_lt (by linarith only [hb.1])
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨rB, cB, hrB, _, hcB, hbranch⟩ := exists_isotropic_positive_branch_curvature α b hα hb hpoint
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let R := min rB (Real.sin b / 4)
  have hR : 0 < R := lt_min hrB (by positivity)
  have hRB : R ≤ rB := min_le_left _ _
  have hRsin : R < Real.sin b / 2 := (min_le_right _ _).trans_lt (by linarith only [hsin])
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hpoint, hcos]
  obtain ⟨rA, cA, hrA, hcA, haway⟩ := exists_fixedPhase_buffer_curvature_tube
    (2 * Real.cos α) b R β η hS hb hpoint hR hβb
  let δ := min β (min rB (rA / 8))
  let c := min cB (cA * Real.sqrt R ^ 3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδβ : δ ≤ β := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  have hδB : δ ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ rA / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, c, hδ, hδβ, by dsimp [c]; positivity, ?_⟩
  intro ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  have hdepth : 0 ≤ τ * ρ := mul_nonneg hτ.1 hρ.1
  have hdepthle : τ * ρ ≤ δ := (mul_le_of_le_one_right hτ.1 hρ.2).trans hτ.2
  have hu : 0 ≤ θ + b := by linarith only [hθ.1]
  have hT : 0 < θ + b + ε + τ * ρ := by linarith only [hu, hε, hdepth]
  have hsT : 0 < Real.sqrt (θ + b + ε + τ * ρ) := Real.sqrt_pos.mpr hT
  by_cases hlocal : θ + b ≤ R
  · have huabs : |θ + b| < Real.sin b / 2 := by rw [abs_of_nonneg hu]; exact hlocal.trans_lt hRsin
    have he := fixedOccupancyPhaseCurvature_geometric_branch (isotropicRadialParameter α ε)
      b η τ ρ υ (θ + b) hη hwidth huabs
    rw [show -b + (θ + b) = θ by ring] at he
    rw [he]
    apply (div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg (Real.sqrt_nonneg _) 3)).trans
    simpa only [show -b + (θ + b) = θ by ring] using
      hbranch ε hε (hεδ.trans hδB) (θ + b) (τ * ρ)
        ⟨hu, hlocal.trans hRB⟩ ⟨hdepth, hdepthle.trans hδB⟩
  · have hfar : R ≤ θ + b := (lt_of_not_ge hlocal).le
    let q : FixedPhaseParameters := (isotropicRadialParameter α ε, τ, ρ, υ, θ)
    let q₀ : FixedPhaseParameters := (((2 * Real.cos α : ℝ) : ℂ), 0, ρ, υ, θ)
    have hq₀ : q₀ ∈ fixedPhaseBufferCompact (2 * Real.cos α) b R β :=
      ⟨rfl, rfl, hρ, hυ, ⟨by linarith only [hfar, hR], hθ.2⟩⟩
    have hdist : dist q q₀ ≤ rA := by
      have hs := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.2
      have hsA : dist (isotropicRadialParameter α ε) (((2 * Real.cos α : ℝ) : ℂ)) ≤ rA :=
        hs.trans (by linarith only [hεδ, hδA, hrA])
      have htA : dist τ (0 : ℝ) ≤ rA := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
        linarith only [hτ.2, hδA, hrA]
      simpa only [q, q₀, Prod.dist_eq, max_le_iff, dist_self] using
        And.intro hsA (And.intro htA hrA.le)
    have hq : q ∈ cthickening rA (fixedPhaseBufferCompact (2 * Real.cos α) b R β) :=
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
