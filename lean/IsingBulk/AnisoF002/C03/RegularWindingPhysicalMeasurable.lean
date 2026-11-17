import IsingBulk.AnisoF002.C03.RegularWindingPhysicalPeriodicity

/-!
# Measurability of the literal complete inner pole coefficient density

The actual pole is continuous on the inner angular set.  Its phase derivative
is obtained as a measurable limit of difference quotients of the original
jointly continuous phase.  No boundedness or nonzero-pole condition is used
to justify measurability of the sharp cutoff.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

theorem actualInnerPoleDensity_measurable_of_joint {b B : ℂ → ℂ}
    {φ r s M kappa rJ : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (hN : 0 < N) (hs : 0 ≤ s)
    (hR : r / (4 * (N : ℝ)) < rJ)
    (hH : ContinuousOn (fun p : ℂ × (Fin N → ℝ) =>
      completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 p.1 (fun i => (p.2 i : ℂ)))
      {p | p.1 ∈ Metric.ball 0 rJ})
    (hF : ContinuousOn (fun p : ℂ × (Fin N → ℝ) => realPhaseAverage B φ N p.2 p.1)
      {p | p.1 ∈ Metric.ball 0 rJ})
    (hFa : ∀ q : Fin N → ℝ, AnalyticOnNhd ℂ (realPhaseAverage B φ N q) (Metric.ball 0 rJ))
    (j : ℕ) : Measurable (actualInnerPoleDensity d j) := by
  let H : ℂ → InnerAngularSet N s → ℂ := fun t q =>
    completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 t (fun i => (q.1 i : ℂ))
  let F : ℂ → InnerAngularSet N s → ℂ := fun t q => realPhaseAverage B φ N q t
  let P : InnerAngularSet N s → ℂ := fun q => d.pole q
  have hHm : Measurable (Function.uncurry (diskKernelExtension rJ H)) :=
    diskKernelExtension_measurable
      (continuousOn_inner_angular_pullback (s := s) hH (Subset.refl _))
  have hFm : Measurable (Function.uncurry (diskKernelExtension rJ F)) :=
    diskKernelExtension_measurable
      (continuousOn_inner_angular_pullback (s := s) hF (Subset.refl _))
  have hPm : Measurable P := (continuousOn_iff_continuous_domRestrict.mp d.pole_continuous).measurable
  have hPin (q : InnerAngularSet N s) : P q ∈ Metric.ball (0 : ℂ) rJ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (d.pole_bound q).trans_lt hR
  have hFd (q : InnerAngularSet N s) : DifferentiableAt ℂ (fun t => F t q) (P q) :=
    (hFa q (P q) (hPin q)).differentiableAt
  have hnear (q : InnerAngularSet N s) :
      (fun t => diskKernelExtension rJ F t q) =ᶠ[𝓝 (P q)] (fun t => F t q) :=
    diskKernelExtension_eventuallyEq F (hPin q) q
  have hDm : Measurable (fun q : InnerAngularSet N s =>
      deriv (fun t => diskKernelExtension rJ F t q) (P q)) :=
    measurable_deriv_at_moving_center hFm hPm
      (fun q => (hFd q).congr_of_eventuallyEq (hnear q))
  let G : InnerAngularSet N s → ℂ := fun q =>
    (2 * diskKernelExtension rJ H (P q) q /
      ((N : ℂ) * deriv (fun t => diskKernelExtension rJ F t q) (P q))) / P q ^ (j + 1)
  have hGm : Measurable G :=
    ((measurable_const.mul (hHm.comp (hPm.prodMk measurable_id))).div
      (measurable_const.mul hDm)).div (hPm.pow_const _)
  have hGe (q : InnerAngularSet N s) :
      G q = d.actualResidue q / d.pole q ^ (j + 1) := by
    unfold G
    rw [diskKernelExtension_eq H (hPin q), (hnear q).deriv_eq]
    change (2 * completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 (d.pole q)
      (fun i => (q.1 i : ℂ)) /
        ((N : ℂ) * deriv (realPhaseAverage B φ N q) (d.pole q))) / d.pole q ^ (j + 1) = _
    rw [← realPhaseTotal_deriv B φ hN q (d.pole q) (hFd q)]
    rfl
  have he : actualInnerPoleDensity d j = fun q =>
      if angularShortSquare q ≤ s then G (innerAngularRetraction N hs q) else 0 := by
    funext q
    by_cases hq : angularShortSquare q ≤ s
    · simp only [actualInnerPoleDensity, shortCutDensity, hq, ↓reduceIte, hGe,
        innerAngularRetraction, innerAngularClip]
    · simp only [actualInnerPoleDensity, shortCutDensity, hq, ↓reduceIte]
  rw [he]
  exact Measurable.ite
    (measurableSet_le (angularShortSquare_continuous N).measurable measurable_const)
    (hGm.comp (innerAngularRetraction_measurable N hs)) measurable_const

theorem exists_actual_inner_pole_density_measurable_radius {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ rJ : ℝ, 0 < rJ ∧ ∀ N : ℕ, 0 < N → ∀ r s M kappa : ℝ,
      ∀ d : InnerRemainderFamily b B φ N r s M kappa,
      0 ≤ s → r / (4 * (N : ℝ)) < rJ → ∀ j : ℕ,
        Measurable (actualInnerPoleDensity d j) := by
  obtain ⟨rJ, hrJ, hJ⟩ := exists_actual_joint_real_factor_control hb hB hφ hπ hBi hbsq
  refine ⟨rJ, hrJ, ?_⟩
  intro N hN r s M kappa d hs hR j
  exact actualInnerPoleDensity_measurable_of_joint d hN hs hR
    (hJ N).1 (hJ N).2.1 (hJ N).2.2 j

end
end IsingBulk.AnisoF002.NegativeHT
