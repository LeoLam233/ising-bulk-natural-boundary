import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorDisks
import IsingBulk.AnisoF002.C03.RegularIsotropicSameSidePairs
import IsingBulk.AnisoF002.C03.IsotropicCurrentNeighborhood

/-!
# The anchored analytic disks on the actual balanced physical image

The only angular gate is a genuine compact-left cosine gap. All root,
inverse-slope and neighborhood hypotheses of the complete regular
density disk are derived from the original physical dispersion.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric
open IsingBulk.AnisoF002.RegularTail

theorem actual_balanced_sin_norm_bound {N : ℕ} (hN : 0 < N) (η τ : ℝ)
    (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) (i : Fin N) :
    ‖Complex.sin (actualHomotopyAngle η τ 1 θ i)‖ ≤ Real.exp 1 := by
  have hdisp := actual_balanced_homotopy_displacement η τ 1 hτ.1 (by norm_num) θ
    (by simpa only [Fintype.card_fin] using hN) i
  have him : |(actualHomotopyAngle η τ 1 θ i).im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (actualHomotopyAngle η τ 1 θ i - (θ i : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact (h.trans hdisp).trans hτ.2
  exact (complex_sin_norm_le_exp_abs_im _).trans (Real.exp_le_exp.mpr him)

theorem exists_actual_anchored_density_disks (α b c : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hc : 0 < c) :
    ∃ β δ ρ κ A K L : ℝ,
      0 < β ∧ β ≤ 1 ∧ 0 < δ ∧ δ ≤ β ∧ 0 < ρ ∧ 0 < κ ∧ 0 < A ∧ 0 < K ∧ 0 < L ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 0 < N → ∀ a : Fin N, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ∈ Icc 0 δ, ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc (-Real.pi - β) β) → c ≤ Real.cos b - Real.cos (θ a) →
      let p := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ 1 θ
      ∀ z ∈ ball p (ρ / (N : ℝ)),
        AnalyticAt ℂ (anchoredRegularField a) z ∧
        (∀ i, AnalyticAt ℂ (fun y => anchoredCutoffCoefficient a y i) z) ∧
        AnalyticAt ℂ (anchoredRegularDensity σ) z ∧
        ‖anchoredRegularField a z‖ ≤ L * N ∧
        (∀ i, ‖anchoredCutoffCoefficient a z i‖ ≤ L * N) ∧
        ‖anchoredRegularDensity σ z‖ ≤
          ‖isotropicParticleNormalization N‖ * K * A ^ N *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  let q₀ := exteriorAnchorRootBound c
  have hq₀ : 0 < q₀ ∧ q₀ < 1 := exteriorAnchorRootBound_spec hc
  let c₀ := 1 / (1 + Real.exp 1 * (2 / (1 - q₀ ^ 2)))
  have hgap : 0 < 1 - q₀ ^ 2 := by nlinarith [hq₀.1, hq₀.2]
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨r, ρ, κ, A, L, hr, hρ, hκ, hA, hL, hdisks⟩ :=
    exists_uniform_anchored_regular_disks (2 * Real.cos α) c₀ q₀ hS hc₀ hq₀.1.le hq₀.2
  obtain ⟨rI, hrI, himage⟩ := exists_actual_oneSided_homotopy_domain (2 * Real.cos α) r hS hr
  obtain ⟨rU, hrU, hdata⟩ := exists_actual_oneSided_inverse_data (2 * Real.cos α) hS
  let β := min 1 (min (rI / 2) (rU / 2))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hbI : β < rI := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hrI)
  have hbU : β < rU := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hrU)
  let δ := min (β / 8) (c / 12)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ8 : δ ≤ β / 8 := min_le_left _ _
  have hdβ : δ ≤ β := hdβ8.trans (by linarith only [hβ])
  have hdc : δ ≤ c / 12 := min_le_right _ _
  have hqgap : 0 < 1 - q₀ := sub_pos.mpr hq₀.2
  refine ⟨β, δ, ρ, κ, A, 4 / (1 - q₀), L, hβ, hβ1, hδ, hdβ, hρ, hκ, hA,
    div_pos (by norm_num) hqgap, hL, ?_⟩
  intro η hη N hN a σ hσ ε hε hεδ τ hτ θ hθ hcos
  let s := isotropicRadialParameter α ε
  let x : ℂ × (Fin N → ℝ) := (s, θ)
  let p := actualHomotopyRegularTuple s η τ 1 θ
  have hε1 : ε ≤ 1 := hεδ.trans (hdβ.trans hβ1)
  have hτ1 : τ ∈ Icc 0 1 := ⟨hτ.1, hτ.2.trans (hdβ.trans hβ1)⟩
  have hrad := isotropicRadialParameter_estimates α ε hα hε hε1
  have hsnear : dist s ((2 * Real.cos α : ℝ) : ℂ) < β :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hdβ8, hβ])
  have hθI : ∀ i, θ i ∈ Icc (-Real.pi - rI) rI :=
    fun i => ⟨by linarith only [(hθ i).1, hbI], (hθ i).2.trans hbI.le⟩
  have hθU : ∀ i, θ i ∈ Icc (-Real.pi - rU) rU :=
    fun i => ⟨by linarith only [(hθ i).1, hbU], (hθ i).2.trans hbU.le⟩
  have hp := (himage N hN s hrad.2.2.2.1 (hsnear.trans hbI) η τ 1 hη
    ⟨hτ.1, hτ.2.trans (hdβ.trans hbI.le)⟩ (by norm_num) θ hθI).1
  have hu := hdata N hN s hrad.2.2.2.1 (hsnear.trans hbU) η τ 1 hη
    ⟨hτ.1, hτ.2.trans (hdβ.trans hbU.le)⟩ (by norm_num) θ hθU
  have hsheet (i : Fin N) := actual_balanced_homotopy_sheet s hrad.2.2.2.1 η τ 1 hη hτ.1 zero_le_one θ i
  have hrootEq (i : Fin N) : regularInverseRoot (p.1, p.2 i) =
      isotropicInteriorRoot (s, actualHomotopyAngle η τ 1 θ i) :=
    regularInverseRoot_actual η τ 1 x i (hu i).2.2.2
  have hrp (i : Fin N) : ‖regularInverseRoot (p.1, p.2 i)‖ ≤ 1 := by
    rw [hrootEq]
    exact (upperEdgeRoot_norm_lt_one (hsheet i)).le
  have hsmall : 4 * ε + 2 * τ ≤ c / 2 := by linarith only [hεδ, hτ.2, hdc]
  have hroot := actual_exterior_anchor_root_bound hN α b ε η τ c hα hpoint hε hε1 hη hτ1 hc hsmall θ a hcos
  have ha : ‖regularInverseRoot (p.1, p.2 a)‖ ≤ q₀ := by rw [hrootEq]; exact hroot
  have hv : c₀ ≤ ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 a)‖ :=
    actual_anchor_inverse_slope_lower a η τ 1 x q₀ (Real.exp 1) hq₀.1.le hq₀.2 (Real.exp_nonneg _)
      (hsheet a) (hu a).1 (hu a).2.1 (hu a).2.2.1 (hu a).2.2.2 hroot
      (actual_balanced_sin_norm_bound hN η τ hτ1 θ a)
  exact hdisks N hN a σ hσ p hp hrp ha hv

end IsingBulk.AnisoF002.Isotropic
