import IsingBulk.AnisoF002.C03.IsotropicActualCovarianceBuffer
import IsingBulk.AnisoF002.C03.IsotropicActualTransportBalls

/-!
# The complete numerator and covariance on a fixed angular buffer

The geometric right interval is chosen before η. Its full protected
numerator and covariance estimates then hold after selecting the small
deformation parameter. The retained Gaussian and complete particle
numerator are the same as in the previously checked single-radius proof.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

 theorem exists_actual_complete_transport_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ κ C M c B : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧ 0 < c ∧ 0 < B ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) → (∃ i j, r ≤ |θ i - θ j|) →
        let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
        let Δ := isotropicShellDelta b ε r θ
        Δ ≤ Real.sqrt (Real.pi + 2) ∧
        ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2),
          AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) p ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ B * (N : ℝ) ^ 2 / Δ ∧
          AnalyticAt ℂ (completeRegularNumerator N) p ∧
          ‖completeRegularNumerator N p‖ ≤
            C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) *
              Δ ^ (2 * R.card) := by
  obtain ⟨δA, hδA, _, hcoordAll⟩ := exists_actual_whole_arc_coordinate_buffer α b hα hb hpoint
  obtain ⟨βB, hβBpos, _, hfieldAll⟩ := exists_actual_covariance_geometric_buffer α b hα hb hpoint
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
  obtain ⟨R₀, κ, C, M, hR₀, hκ, hC, hM, hnum⟩ :=
    exists_completeNumerator_collision_ball (2 * Real.cos α) hS
  obtain ⟨δD, hδD, hdomain⟩ := exists_actual_right_homotopy_domain
    (2 * Real.cos α) (R₀ / 2) hS (half_pos hR₀)
  let β := min 1 (min δA (min βB (δD / 8)))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβA : β ≤ δA := (min_le_right _ _).trans (min_le_left _ _)
  have hβB : β ≤ βB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hβD8 : β ≤ δD / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hβD' : β ≤ δD := by linarith only [hβD8, hδD]
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨A, hA, hcoord⟩ := hcoordAll η hη hwidth
  obtain ⟨δB, cB, B, hδB, _, hcB, hB, hfield⟩ := hfieldAll η hη hwidth
  let δ := min β δB
  let c := min cB (min 1 (R₀ / (2 * D₀)))
  let M₁ := (A + 2) ^ 2 * M
  have hδ : 0 < δ := lt_min hβ hδB
  have hδβ : δ ≤ β := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  have hδA' : δ ≤ δA := hδβ.trans hβA
  have hδB' : δ ≤ δB := min_le_right _ _
  have hδD8 : δ ≤ δD / 8 := hδβ.trans hβD8
  have hδD' : δ ≤ δD := hδβ.trans hβD'
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB' : c ≤ cB := min_le_left _ _
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcR : c * D₀ ≤ R₀ / 2 := by
    have hh : c ≤ R₀ / (2 * D₀) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 2 * D₀ by positivity)).mp hh
    nlinarith only [hh']
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨δ, κ, C, M₁, c, B, hδ, hδβ, hκ, hC, hM₁, hc, hB, ?_⟩
  intro N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δD :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδD8, hδD])
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δD) δD := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hβD'], (hθ i).2.trans hβD'⟩
  have hq : q ∈ rightProductDomain (2 * Real.cos α) (R₀ / 2) N :=
    (hdomain N hN _ hrad.2.2.2.1 hsnear η τ ξ hη
      ⟨hτ.1, hτ.2.trans hδD'⟩ hξ θ hθD).1
  have hcoord' (i j : Fin N) : ‖q.2 i - q.2 j‖ ≤ A * Δ := by
    have hh := hcoord N hN ε hε (hεδ.trans hδA') τ ξ ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
      (fun l => ⟨by linarith only [(hθ l).1, hb.2, hβA], (hθ l).2.trans hβA⟩) r hr hdiam i j
    exact hh.trans_eq (by dsimp [Δ, isotropicShellDelta, isotropicShellT]; ring)
  have hrmax : r ≤ Real.pi + 2 := by
    obtain ⟨i, j, hij⟩ := hdiamLower
    have hg : |θ i - θ j| ≤ b + 2 * β :=
      abs_le.mpr ⟨by linarith only [(hθ i).1, (hθ j).2],
        by linarith only [(hθ i).2, (hθ j).1]⟩
    linarith only [hij, hg, hb.2, hβ1]
  have hT : 0 < isotropicShellT b ε r θ := by unfold isotropicShellT; positivity
  have hrT : r ≤ isotropicShellT b ε r θ := by
    unfold isotropicShellT
    linarith only [abs_nonneg (angularMean (fun l => θ l + b)), hε]
  have hΔroot : Δ ≤ Real.sqrt r := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hT)).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrT) (Real.sqrt_nonneg r)
    simpa only [Real.mul_self_sqrt hr.le] using hh
  have hΔD : Δ ≤ D₀ := hΔroot.trans (Real.sqrt_le_sqrt hrmax)
  refine ⟨hΔD, ?_⟩
  intro p hp
  have hρle : c * Δ / (N : ℝ) ^ 2 ≤ c * Δ :=
    div_le_self (mul_nonneg hc.le hΔ.le) (one_le_pow₀ hN1)
  have hρΔ : c * Δ / (N : ℝ) ^ 2 ≤ Δ :=
    hρle.trans (by nlinarith only [hc1, hΔ])
  have hρR : c * Δ / (N : ℝ) ^ 2 ≤ R₀ / 2 :=
    hρle.trans ((mul_le_mul_of_nonneg_left hΔD hc.le).trans hcR)
  have hnumP := hnum N R hR q hq A Δ (c * Δ / (N : ℝ) ^ 2) hA.le hΔ
    (by positivity) hρΔ hρR hcoord' p hp
  have hpB : p ∈ ball q (cB * Δ / (N : ℝ) ^ 2) :=
    ball_subset_ball (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcB' hΔ.le)
      (by positivity)) hp
  have hfieldP := (hfield N hN ε hε (hεδ.trans hδB') τ ξ
    ⟨hτ.1, hτ.2.trans hδB'⟩ hξ θ
    (fun i => ⟨by linarith only [(hθ i).1, hβB], (hθ i).2.trans hβB⟩)
    r hr hdiam hdiamLower).1 p hpB
  refine ⟨hfieldP.1, hfieldP.2.2, hnumP.1, hnumP.2.trans_eq ?_⟩
  have hpow : M₁ ^ R.card = (A + 2) ^ (2 * R.card) * M ^ R.card := by
    dsimp only [M₁]
    rw [mul_pow, ← pow_mul]
  rw [hpow]
  ring


end IsingBulk.AnisoF002.Isotropic
