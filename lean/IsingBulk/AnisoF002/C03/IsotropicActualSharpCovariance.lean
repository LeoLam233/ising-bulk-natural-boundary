import IsingBulk.AnisoF002.C03.IsotropicActualShellVariance
import IsingBulk.AnisoF002.C03.IsotropicSharpCovarianceDisks

/-!
# Sharp covariance disks on the actual F002 right shells

All input scales are discharged on the actual balanced tuple. This is
the covariance-field part of the frozen protected-variance and joint-jet
lemma, with one neighborhood and constants before every particle number.
It does not assert the remaining angular-frame or integrated coarea bounds.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def isotropicShellT {N : ℕ} (b ε r : ℝ) (θ : Fin N → ℝ) : ℝ :=
  |angularMean (fun k => θ k + b)| + r + ε

def isotropicShellDelta {N : ℕ} (b ε r : ℝ) (θ : Fin N → ℝ) : ℝ :=
  r / Real.sqrt (isotropicShellT b ε r θ)

theorem isotropicShellDelta_pos {N : ℕ} (b ε r : ℝ) (θ : Fin N → ℝ)
    (hε : 0 < ε) (hr : 0 < r) : 0 < isotropicShellDelta b ε r θ := by
  unfold isotropicShellDelta isotropicShellT
  positivity

/-- Sharp protected variance, the complete filled covariance field,
and every fixed joint jet on each actual right diameter shell. Proper
partial coincidences are included; only total equality is off-shell. -/
theorem exists_actual_right_shell_covariance_disks (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ c B : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < B ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) → (∃ i j, r ≤ |θ i - θ j|) →
        let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
        let Δ := isotropicShellDelta b ε r θ
        (∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2),
          AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
          r ^ 2 / 8 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ B * (N : ℝ) ^ 2 / Δ) ∧
        ∀ k : ℕ,
          ‖iteratedFDeriv ℂ k (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q‖ ≤
            protectedJetConstant k (c * Δ / (N : ℝ) ^ 2) * (B * (N : ℝ) ^ 2 / Δ) := by
  obtain ⟨δA, A, hδA, _, hA, hcoord⟩ :=
    exists_actual_whole_arc_shell_coordinate_scale α b η hα hb hpoint hη hwidth
  obtain ⟨δK, K, hδK, _, hK, hslope⟩ :=
    exists_actual_right_shell_inverse_coordinate_scale α b hα hb hpoint
  obtain ⟨δV, hδV, hvar⟩ := exists_actual_shell_variance_control η
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
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨R, c, B, hR, hc, hB, hdisks⟩ :=
    exists_right_sharp_covariance_disks (2 * Real.cos α) A K D₀ hS hA hK hD₀
  obtain ⟨δD, hδD, hdomain⟩ := exists_actual_right_homotopy_domain
    (2 * Real.cos α) (R / 2) hS (half_pos hR)
  let δ := min 1 (min δA (min δK (min δV (δD / 8))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδA' : δ ≤ δA := (min_le_right _ _).trans (min_le_left _ _)
  have hδK' : δ ≤ δK := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδV' : δ ≤ δV := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδD8 : δ ≤ δD / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδD' : δ ≤ δD := by linarith only [hδD8, hδD]
  refine ⟨δ, c, B, hδ, hδ1, hc, hB, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
  let T := isotropicShellT b ε r θ
  let t := Real.sqrt T
  let Δ := isotropicShellDelta b ε r θ
  have hT : 0 < T := by dsimp [T, isotropicShellT]; positivity
  have ht : 0 < t := Real.sqrt_pos.mpr hT
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have htΔ : t * Δ = r := by
    change t * (r / t) = r
    field_simp [ht.ne']
  have hrT : r ≤ T := by dsimp [T, isotropicShellT]; linarith only [abs_nonneg (angularMean (fun k => θ k + b)), hε]
  have hΔt : Δ ≤ t := by
    apply (div_le_iff₀ ht).mpr
    simpa only [t, pow_two, Real.mul_self_sqrt hT.le] using hrT
  have hrmax : r ≤ Real.pi + 2 := by
    obtain ⟨i, j, hij⟩ := hdiamLower
    have hg : |θ i - θ j| ≤ b + 2 * δ := by
      exact abs_le.mpr ⟨by linarith only [(hθ i).1, (hθ j).2],
        by linarith only [(hθ i).2, (hθ j).1]⟩
    linarith only [hij, hg, hb.2, hδ1]
  have hΔroot : Δ ≤ Real.sqrt r := by
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrT) (Real.sqrt_nonneg r)
    simpa only [Real.mul_self_sqrt hr.le] using hh
  have hΔD : Δ ≤ D₀ := hΔroot.trans (Real.sqrt_le_sqrt hrmax)
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δD :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδD8, hδD])
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δD) δD := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδD'], (hθ i).2.trans hδD'⟩
  obtain ⟨hq, heq⟩ := hdomain N hN _ hrad.2.2.2.1 hsnear η τ ξ hη
    ⟨hτ.1, hτ.2.trans hδD'⟩ hξ θ hθD
  have heq' (i : Fin N) : explicitRightInverse (q.1, q.2 i) = actualHomotopyAngle η τ ξ θ i := heq i
  have hcoord' (i j : Fin N) : ‖q.2 i - q.2 j‖ ≤ A * Δ := by
    have hh := hcoord N hN ε hε (hεδ.trans hδA') τ ξ ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
      (fun k => ⟨by linarith only [(hθ k).1, hb.2, hδA'], (hθ k).2.trans hδA'⟩) r hr hdiam i j
    exact hh.trans_eq (by dsimp [Δ, isotropicShellDelta, isotropicShellT]; ring)
  have hslope' (i : Fin N) : ‖deriv (fun z => explicitRightInverse (q.1, z)) (q.2 i)‖ ≤ K * t :=
    hslope N hN ε hε (hεδ.trans hδK') η τ ξ hη ⟨hτ.1, hτ.2.trans hδK'⟩ hξ θ
      (fun k => ⟨by linarith only [(hθ k).1, hδK'], (hθ k).2.trans hδK'⟩) r hr hdiam i
  obtain ⟨hpair, hvarlower⟩ := hvar N hN τ ⟨hτ.1, hτ.2.trans hδV'⟩ ξ hξ θ
  have hdiff (i j : Fin N) :
      ‖explicitRightInverse (q.1, q.2 i) - explicitRightInverse (q.1, q.2 j)‖ ≤ 4 * r := by
    rw [heq' i, heq' j]
    exact (hpair i j).trans (by linarith only [hdiam i j])
  have hvariance : r ^ 2 / 4 ≤ (pairVariance (fun i => explicitRightInverse (q.1, q.2 i))).re := by
    have hf : (fun i => explicitRightInverse (q.1, q.2 i)) = actualHomotopyAngle η τ ξ θ := funext heq'
    rw [hf]
    exact hvarlower r hr hdiamLower
  exact hdisks N hN q hq r t Δ hr ht hΔ htΔ hΔt hΔD hcoord' hslope' hdiff hvariance

end IsingBulk.AnisoF002.Isotropic
