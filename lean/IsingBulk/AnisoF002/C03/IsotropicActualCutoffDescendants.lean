import IsingBulk.AnisoF002.C03.IsotropicSeparatedWordSumBounds
import IsingBulk.AnisoF002.C03.IsotropicInverseVelocityGerm
import IsingBulk.AnisoF002.C03.IsotropicActualCutoffBalls
import IsingBulk.AnisoF002.C03.IsotropicActualUnweightedTransport

/-!
# Full normalized actual descendants with arbitrary smooth angular weights

The full actual recurrence is bounded after every coefficient and cutoff
has been differentiated. The quantitative cutoff input is ordinary real
finite-jet control; all physical-image, analytic, inverse, and current
data are constructed on one common neighborhood before N and the order.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Set Metric

theorem exists_actual_normalized_cutoff_descendant_bound (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ (g : (Fin N → ℝ) → ℂ) (Cg : ℝ), 0 ≤ Cg → ContDiff ℝ ∞ g → FiniteJetControl j g Cg →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i l, |θ i - θ l| ≤ 2 * r) → (∃ i l, r ≤ |θ i - θ l|) →
        let Δ := isotropicShellDelta b ε r θ
        ‖actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ (fun y => g y.2)) j
          (isotropicRadialParameter α ε, θ)‖ ≤
          (Cj * (N : ℝ) ^ ((7 + 3 * j) * j) * C ^ N * M ^ R.card *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) * Cg *
              Δ ^ (2 * R.card) / Δ ^ (2 * j)) /
            ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1)) := by
  obtain ⟨δA, κ, C, M, c, B, K, hδA, hδA1, hκ, hC, hM, hc, hB, hK, hballs⟩ :=
    exists_actual_complete_cutoff_transport_balls α b η hα hb hpoint hη hwidth
  obtain ⟨δE, hδE, _, hinv⟩ := exists_actual_inverse_entries_all_angular_jets η
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
  obtain ⟨δD, hδD, hdata⟩ := exists_actual_right_current_data (2 * Real.cos α) η hS hη
  obtain ⟨δV, hδV, _, hvel⟩ := exists_actual_inverse_velocity_germ (2 * Real.cos α) η hS hη
  let δ := min δA (min δE (min (δD / 8) (δV / 8)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA' : δ ≤ δA := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδA'.trans hδA1
  have hδE' : δ ≤ δE := (min_le_right _ _).trans (min_le_left _ _)
  have hδD8 : δ ≤ δD / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδV8 : δ ≤ δV / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδD' : δ ≤ δD := by linarith only [hδD8, hδD]
  have hδV' : δ ≤ δV := by linarith only [hδV8, hδV]
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨δ, κ, C, M, hδ, hδ1, hκ, hC, hM, ?_⟩
  intro j
  obtain ⟨CA₀, _, hA₀⟩ := hinv j
  let CA := max 1 CA₀
  have hCA : 1 ≤ CA := le_max_left _ _
  refine ⟨separatedWordBoundConstant j j c B K D₀ CA,
    separatedWordBoundConstant_pos j j c B K D₀ CA hc hB hK hD₀ (zero_lt_one.trans_le hCA), ?_⟩
  intro N hN R hR g Cg hCg hg hgj ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let s := isotropicRadialParameter α ε
  let x := (s, θ)
  let q := actualHomotopyRegularTuple s η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  let F : RegularJointSpace N → ℂ := fun p => isotropicParticleNormalization N * completeRegularNumerator N p
  let E₀ := ‖isotropicParticleNormalization N‖ * C ^ N * M ^ R.card *
    Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  obtain ⟨hΔD, hball⟩ := hballs N hN R hR ε hε (hεδ.trans hδA') τ ξ
    ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
    (fun i => ⟨by linarith only [(hθ i).1, hδA'], (hθ i).2.trans hδA'⟩)
    r hr hdiam hdiamLower
  have hqball : q ∈ ball q (c * Δ / (N : ℝ) ^ 2) := mem_ball_self (by positivity)
  have hFa : AnalyticOnNhd ℂ F (ball q (c * Δ / (N : ℝ) ^ 2)) :=
    fun p hp => analyticAt_const.mul (hball p hp).2.2.1
  have hFb : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤ E₀ * Δ ^ (2 * R.card) := by
    intro p hp
    rw [show F p = isotropicParticleNormalization N * completeRegularNumerator N p from rfl, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hball p hp).2.2.2.1 (norm_nonneg _)).trans_eq (by dsimp [E₀]; ring)
  have hA : ∀ i l : Fin N, FiniteJetControl j (actualBalancedInverseEntry η τ ξ i l)
      (CA * (N : ℝ) ^ (3 * j)) := by
    intro i l
    exact (hA₀ N hN τ ξ ⟨hτ.1, hτ.2.trans hδE'⟩ hξ i l).mono_bound
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hAsmooth (i l : Fin N) : ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i l) := by
    apply contDiff_infty.mpr
    intro k
    obtain ⟨CAk, _, hAk⟩ := hinv k
    exact (hAk N hN τ ξ ⟨hτ.1, hτ.2.trans hδE'⟩ hξ i l).smooth
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsD : dist s ((2 * Real.cos α : ℝ) : ℂ) < δD :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδD8, hδD])
  have hsV : dist s ((2 * Real.cos α : ℝ) : ℂ) < δV :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδV8, hδV])
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δD) δD := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδD'], (hθ i).2.trans hδD'⟩
  have hθV : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δV) δV := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδV'], (hθ i).2.trans hδV'⟩
  obtain ⟨i, l, hil⟩ := hdiamLower
  have hneq : θ i ≠ θ l := by intro he; rw [he, sub_self, abs_zero] at hil; linarith only [hil, hr]
  obtain ⟨hχ, hdet, _⟩ := hdata N hN s hrad.2.2.2.1 hsD τ ⟨hτ.1, hτ.2.trans hδD'⟩
    ξ hξ θ hθD i l hneq
  have hV := (hvel N hN s hrad.2.2.2.1 hsV τ ξ ⟨hτ.1, hτ.2.trans hδV'⟩ hξ θ hθV).2 hdet
  have he := actualTransportDescendant_eq_separated_words η τ ξ F g hAsmooth hg x hχ
    (hball q hqball).1 (fun l => ((hball q hqball).2.2.2.2 l).1) (hFa q hqball) hdet hV j
  have hinit : actualInitialAmplitude η τ ξ (fun y : ℂ × (Fin N → ℝ) => g y.2) =
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) := by
    funext y
    change isotropicParticleNormalization N * g y.2 * completeRegularNumerator N _ =
      (isotropicParticleNormalization N * completeRegularNumerator N _) * g y.2
    dsimp only [regularJointMap]
    ring
  rw [hinit, he]
  have hbound := separatedWordSum_scaled_bound hN
    (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) rightCutoffTransportCoefficient F
    (actualBalancedInverseEntry η τ ξ) g q θ c B K D₀ Δ E₀ CA Cg (2 * R.card) j j le_rfl
    hc hB hK hD₀ hΔ hΔD hE₀ hCA hCg (fun p hp => (hball p hp).1)
    (fun l p hp => ((hball p hp).2.2.2.2 l).1) hFa (fun p hp => (hball p hp).2.1)
    (fun p hp l => ((hball p hp).2.2.2.2 l).2) hFb hA hgj
  exact hbound.trans_eq (by dsimp [E₀]; rw [isotropicParticleNormalization_norm]; ring)

end IsingBulk.AnisoF002.Isotropic
