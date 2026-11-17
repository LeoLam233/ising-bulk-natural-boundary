import IsingBulk.AnisoF002.C03.RegularIsotropicActualAnchorDisks
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchoredDensity
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorWordBounds

/-!
# All complete anchored transport amplitudes on the actual physical image

One deformation radius precedes derivative order and population. The
bound differentiates the full product kernel and includes every real
cutoff derivative and every entry of the balanced inverse Jacobian.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Metric Filter

def anchorJetPolynomialOrder (j : ℕ) : ℕ := 2 * j + 3 * j + 3 * j * j + 2 * j

theorem exists_actual_complete_anchor_amplitudes (α b c : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hc : 0 < c) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ κ A : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < κ ∧ 0 < A ∧
      ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧
      ∀ N : ℕ, 0 < N → ∀ a : Fin N, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ G D : ℝ, 0 ≤ G → 0 ≤ D → ∀ g : (Fin N → ℝ) → ℂ,
      ContDiff ℝ ∞ g → FiniteJetControl j g (G * D ^ N * (N : ℝ) ^ (2 * j)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ∈ Icc 0 δ, ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc (-Real.pi - β) β) → c ≤ Real.cos b - Real.cos (θ a) →
        ‖anchoredTransportDescendant a σ η τ 1 g j (isotropicRadialParameter α ε, θ)‖ ≤
          G * Cj * ‖isotropicParticleNormalization N‖ * (A * D) ^ N *
            (N : ℝ) ^ anchorJetPolynomialOrder j *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨βD, δD, ρ, κ, A, K, L, hβD, hβD1, hδD, _, hρ, hκ, hA, hK, hL, hdisks⟩ :=
    exists_actual_anchored_density_disks α b c hα hb hpoint hc
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  obtain ⟨βF, hβF, _, hframes⟩ := exists_actual_anchored_frame_buffer (2 * Real.cos α) hS
  let β := min βD βF
  have hβ : 0 < β := lt_min hβD hβF
  have hbD : β ≤ βD := min_le_left _ _
  have hbF : β ≤ βF := min_le_right _ _
  have hβ1 : β ≤ 1 := hbD.trans hβD1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δF, hδF, _, hjets, hframe⟩ := hframes η hη
  let δ := min β (min δD (δF / 8))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdD : δ ≤ δD := (min_le_right _ _).trans (min_le_left _ _)
  have hdF8 : δ ≤ δF / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hdF : δ ≤ δF := by linarith only [hdF8, hδF]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, κ, A, hδ, hdβ, hκ, hA, ?_⟩
  intro j
  obtain ⟨CA₀, _, hAj⟩ := hjets j
  let CA := max 1 CA₀
  have hCA : 1 ≤ CA := le_max_left _ _
  refine ⟨anchorWordCost j ρ L CA 1 * K,
    mul_pos (anchorWordCost_pos j hρ hL (zero_lt_one.trans_le hCA) zero_lt_one) hK, ?_⟩
  intro N hN a σ hσ G D hG hD g hg hgj ε hε hεδ τ hτ θ hθ hcos
  let s := isotropicRadialParameter α ε
  let x : ℂ × (Fin N → ℝ) := (s, θ)
  let p : RegularJointSpace N := regularJointMap (actualPhysicalCoordinate η τ 1) x
  let M := ‖isotropicParticleNormalization N‖ * K * A ^ N *
    Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hball := hdisks η hη N hN a σ hσ ε hε (hεδ.trans hdD) τ
    ⟨hτ.1, hτ.2.trans hdD⟩ θ
    (fun i => ⟨by linarith only [(hθ i).1, hbD], (hθ i).2.trans hbD⟩) hcos
  have hp : p ∈ ball p (ρ / N) := mem_ball_self (by positivity)
  have hAjet (i l : Fin N) : FiniteJetControl j (actualBalancedInverseEntry η τ 1 i l)
      (CA * (N : ℝ) ^ (3 * j)) :=
    (hAj N hN τ 1 ⟨hτ.1, hτ.2.trans hdF⟩ (by norm_num) i l).mono_bound
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hAsmooth (i l : Fin N) : ContDiff ℝ ∞ (actualBalancedInverseEntry η τ 1 i l) := by
    apply contDiff_infty.mpr
    intro k
    obtain ⟨Ck, _, hk⟩ := hjets k
    exact (hk N hN τ 1 ⟨hτ.1, hτ.2.trans hdF⟩ (by norm_num) i l).smooth
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hd1)
  have hsnear : dist s ((2 * Real.cos α : ℝ) : ℂ) < δF :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hdF8, hδF])
  obtain ⟨hχ, hdet, _, hB, hKK, hV⟩ := hframe N hN s hrad.2.2.2.1 hsnear τ 1
    ⟨hτ.1, hτ.2.trans hdF⟩ (by norm_num) θ
    (fun i => ⟨by linarith only [(hθ i).1, hbF], (hθ i).2.trans hbF⟩) a
  have he := coordinateTransportDescendant_eq_separated_words (anchoredRegularField a)
    (anchoredCutoffCoefficient a) η τ 1 (anchoredRegularDensity σ) g hAsmooth hg x
    (fun i => (hχ i).of_le (by simp)) hB hKK (hball p hp).2.2.1 hdet
    (hV.mono (fun _ hy => hy.2)) j
  change ‖coordinateTransportDescendant (anchoredRegularField a) η τ 1
    (fun y => anchoredRegularDensity σ (regularJointMap (actualPhysicalCoordinate η τ 1) y) * g y.2) j x‖ ≤ _
  rw [he]
  have hh := coordinateSeparatedWordSum_anchor_bound hN (anchoredRegularField a)
    (anchoredCutoffCoefficient a) (anchoredRegularDensity σ) η τ 1 g x ρ L M CA G D j (2 * j)
    hρ hL.le hM hCA hG hD (fun z hz => (hball z hz).1)
    (fun i z hz => (hball z hz).2.1 i) (fun z hz => (hball z hz).2.2.1)
    (fun z hz => (hball z hz).2.2.2.1) (fun z hz i => (hball z hz).2.2.2.2.1 i)
    (fun z hz => (hball z hz).2.2.2.2.2) hAjet hgj
  exact hh.trans_eq (by
    dsimp [anchorWordCost, M, anchorJetPolynomialOrder]
    rw [mul_pow]
    ring)

end IsingBulk.AnisoF002.Isotropic
