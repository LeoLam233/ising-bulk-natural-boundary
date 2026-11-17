import IsingBulk.AnisoF002.C03.IsotropicNonresonantLocalDensity
import IsingBulk.AnisoF002.C03.IsotropicCompactWeightedHolomorphy
import IsingBulk.AnisoF002.C03.IsotropicFirstPlateau

/-!
# Genuine analytic continuation of actual nonresonant near-coincidence integrals

The common chart radius is chosen before the real angular weight.  Every
continuous weight supported in the resulting constrained quadratic ball
gives an analytic continuation of its actual full deformed coefficient.
The angular Jacobian and all original normalization factors are retained.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem actualHomotopyAngle_constant (N : ℕ) (η τ ξ μ : ℝ) :
    actualHomotopyAngle η τ ξ (fun _ : Fin N => μ) = fun _ => (μ : ℂ) := by
  funext i
  rw [actualHomotopyAngle_affine_time]
  simp only [actualHomotopyDisplacement, balancedShift_of_constant, Complex.ofReal_zero,
    mul_zero, sub_zero]

theorem centeredConstraintAngles_zero (n : ℕ) (μ : ℝ) :
    centeredConstraintAngles μ (0 : Fin n → ℝ) = fun _ => μ := by
  funext i
  change μ + (NegativeHT.Angular.independentChart n (0 : Fin n → ℝ) :
    NegativeHT.Angular.Ambient n) i = μ
  rw [map_zero]
  change μ + 0 = μ
  exact add_zero μ

theorem exists_actual_nonresonant_centered_kernel_buffer (n : ℕ) (S₀ μ η τ ξ : ℝ) (σ : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hx : -1 < S₀ - Real.cos μ) (hx1 : S₀ - Real.cos μ ≠ 1)
    (hden : 1 - σ * upperBoundaryRoot (S₀ - Real.cos μ) ^ (n + 1) ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : Fin n → ℝ, ‖q‖ ≤ d →
      AnalyticAt ℂ (isotropicRootPhysicalDensity
        (isotropicNonbranchLocalRoot (S₀ - Real.cos μ)) σ)
        ((S₀ : ℂ), actualHomotopyAngle η τ ξ (centeredConstraintAngles μ q)) ∧
      ∀ S : ℂ, dist S (S₀ : ℂ) ≤ d → 0 < S.im →
        isotropicRootPhysicalDensity (isotropicNonbranchLocalRoot (S₀ - Real.cos μ)) σ
          (S, actualHomotopyAngle η τ ξ (centeredConstraintAngles μ q)) =
        isotropicBarePhysicalDensity S σ (actualHomotopyAngle η τ ξ (centeredConstraintAngles μ q)) := by
  let W := fun q : Fin n → ℝ => actualHomotopyAngle η τ ξ (centeredConstraintAngles μ q)
  have hW : Continuous W :=
    (actualHomotopyAngles_continuous η τ ξ).comp (centeredConstraintAngles_continuous μ)
  have hW0 : W 0 = fun _ => (μ : ℂ) := by
    dsimp only [W]
    rw [centeredConstraintAngles_zero, actualHomotopyAngle_constant]
  have hmap : Continuous (fun p : ℂ × (Fin n → ℝ) => (p.1, W p.2)) :=
    continuous_fst.prodMk (hW.comp continuous_snd)
  have hbase := (isotropicNonresonantLocalDensity_analyticAt (N := n + 1) S₀ μ σ hx hx1 hden).eventually_analyticAt
  have heq := isotropicNonresonantLocalDensity_matches_upper (N := n + 1) S₀ μ σ hx hx1
  have ht : Tendsto (fun p : ℂ × (Fin n → ℝ) => (p.1, W p.2))
      (𝓝 ((S₀ : ℂ), 0)) (𝓝 ((S₀ : ℂ), fun _ => (μ : ℂ))) := by
    simpa only [hW0] using hmap.continuousAt.tendsto (x := ((S₀ : ℂ), 0))
  obtain ⟨e, he, hev⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (hbase.and heq))
  refine ⟨e / 2, half_pos he, ?_⟩
  intro q hq
  have hdist (S : ℂ) (hS : dist S (S₀ : ℂ) ≤ e / 2) :
      dist (S, q) ((S₀ : ℂ), (0 : Fin n → ℝ)) < e := by
    rw [Prod.dist_eq, max_lt_iff, dist_zero_right]
    exact ⟨hS.trans_lt (half_lt_self he), hq.trans_lt (half_lt_self he)⟩
  refine ⟨(hev (hdist (S₀ : ℂ) (by simpa only [dist_self] using (half_pos he).le))).1, ?_⟩
  intro S hS him
  exact (hev (hdist S hS)).2
    (fun i => actual_balanced_homotopy_sheet S him η τ ξ hη hτ hξ (centeredConstraintAngles μ q) i)

def isotropicLocalWeightedFamily {N : ℕ} (R : ℂ → ℂ) (σ : ℂ)
    (p : ℂ × (ℂ × (Fin N → ℂ))) : ℂ :=
  p.2.1 * isotropicRootPhysicalDensity R σ (p.1, p.2.2)

theorem isotropicLocalWeightedFamily_analyticAt {N : ℕ} (R : ℂ → ℂ) (σ : ℂ)
    (S c : ℂ) (w : Fin N → ℂ)
    (hF : AnalyticAt ℂ (isotropicRootPhysicalDensity R σ) (S, w)) :
    AnalyticAt ℂ (isotropicLocalWeightedFamily R σ) (S, c, w) := by
  have ha : AnalyticAt ℂ (fun p : ℂ × (ℂ × (Fin N → ℂ)) => p.2.1) (S, c, w) :=
    analyticAt_fst.comp analyticAt_snd
  have hm : AnalyticAt ℂ (fun p : ℂ × (ℂ × (Fin N → ℂ)) => (p.1, p.2.2)) (S, c, w) :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hc : AnalyticAt ℂ (fun p : ℂ × (ℂ × (Fin N → ℂ)) =>
      isotropicRootPhysicalDensity (N := N) R σ (p.1, p.2.2)) (S, c, w) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (g := isotropicRootPhysicalDensity (N := N) R σ)
        (f := fun p : ℂ × (ℂ × (Fin N → ℂ)) => (p.1, p.2.2))
        (x := (S, c, w)) hF hm)
  exact ha.mul hc

/-- A continuation of the actual full coefficient for every sufficiently
small real near-coincidence weight.  The radius precedes that weight. -/
theorem exists_actual_nonresonant_coincidence_extension (n : ℕ) (S₀ μ η τ ξ : ℝ) (σ : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hx : -1 < S₀ - Real.cos μ) (hx1 : S₀ - Real.cos μ ≠ 1)
    (hden : 1 - σ * upperBoundaryRoot (S₀ - Real.cos μ) ^ (n + 1) ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℝ, 0 < R → R ≤ d ^ 2 →
      ∀ g : (Fin (n + 1) → ℝ) → ℂ, Continuous g →
        (∀ q : Fin n → ℝ, g (centeredConstraintAngles μ q) ≠ 0 →
          angularQuadratic (flatConstrainedAngles q) ≤ R) →
        ∃ G : ℂ → ℂ, AnalyticAt ℂ G (S₀ : ℂ) ∧
          ∀ S : ℂ, dist S (S₀ : ℂ) ≤ d → 0 < S.im →
            G S = centeredWeightedPhysicalCoefficient η τ ξ μ σ g S := by
  obtain ⟨d, hd, hkernel⟩ := exists_actual_nonresonant_centered_kernel_buffer
    n S₀ μ η τ ξ σ hη hτ hξ hx hx1 hden
  refine ⟨d, hd, ?_⟩
  intro R hR hRd g hg hsupp
  let K := isotropicFirstShapeClosedBall n R
  let L := isotropicNonbranchLocalRoot (S₀ - Real.cos μ)
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun q =>
    (g (centeredConstraintAngles μ q) *
      (actualBalancedJacobian η τ ξ (centeredConstraintAngles μ q)).det,
      actualHomotopyAngle η τ ξ (centeredConstraintAngles μ q))
  let G : ℂ → ℂ := fun S => ∫ q in K, isotropicLocalWeightedFamily L σ (S, H q)
  have hK : IsCompact K := isotropicFirstShapeClosedBall_compact n hR.le
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := ((hg.mul (actualBalancedJacobian_det_continuous η τ ξ)).prodMk
    (actualHomotopyAngles_continuous η τ ξ)).comp (centeredConstraintAngles_continuous μ)
  have hqnorm (q : Fin n → ℝ) (hq : q ∈ K) : ‖q‖ ≤ d := by
    have hlow := flatConstrainedAngles_quadratic_lower q
    change angularQuadratic (flatConstrainedAngles q) ≤ R at hq
    nlinarith [norm_nonneg q]
  refine ⟨G, ?_, ?_⟩
  · apply analyticAt_integral_of_joint_analytic hK (ae_restrict_mem hK.isClosed.measurableSet) hH
    intro q hq
    exact isotropicLocalWeightedFamily_analyticAt L σ _ _ _ (hkernel q (hqnorm q hq)).1
  · intro S hS him
    have heq : G S = ∫ q in K, g (centeredConstraintAngles μ q) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, centeredConstraintAngles μ q) := by
      apply setIntegral_congr_fun hK.isClosed.measurableSet
      intro q hq
      dsimp only [isotropicLocalWeightedFamily, H, L]
      rw [(hkernel q (hqnorm q hq)).2 S hS him, homotopyPulledDensity_actual]
      ring
    rw [heq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz : g (centeredConstraintAngles μ q) = 0 := by
      by_contra hn
      exact hq (hsupp q hn)
    rw [hz, zero_mul]

end
end IsingBulk.AnisoF002.Isotropic
