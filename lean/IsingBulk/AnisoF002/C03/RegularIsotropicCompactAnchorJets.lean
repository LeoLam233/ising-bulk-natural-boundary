import IsingBulk.AnisoF002.C03.RegularIsotropicActualAnchorAmplitudes
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorCoefficientJets
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorJacobian
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorSupport
import IsingBulk.AnisoF002.C03.IsotropicNamedProductIntegral
import IsingBulk.AnisoF002.C03.IsotropicRightGaussianSummability

/-!
# Uniform Gaussian bounds for every actual compact anchored coefficient jet

The named coordinate is eliminated with its exact constrained Jacobian.
Every other inverse-sine factor is integrated independently. The full
balanced determinant, the entire product kernel, every pair, every real
cutoff derivative and the original normalization are retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter Metric MeasureTheory

theorem exists_actual_compact_anchor_gaussian_jets (α b δB : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hδB : 0 < δB) (hleft : b + δB < Real.pi) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ β → RightCutoffGeometry b δB ρ →
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → 2 * η ≤ Real.sin (ρ / 2) →
      ∃ δ κ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧
      ∀ j : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ n : ℕ, ∀ a : Fin (n + 2), ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ τ ∈ Icc 0 δ, ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ 1 μ σ
          (actualLowerCompactAnchorCutoff η b δB ρ a)) (isotropicRadialParameter α ε)‖ ≤
          rightGaussianCoefficientEnvelope κ A B (anchorJetPolynomialOrder j) (n + 2) := by
  let c := Real.cos b - Real.cos (b + δB / 2)
  have hc : 0 < c := actual_anchor_cosine_constant_pos hb.1 hδB hleft
  obtain ⟨βA, hβA, hβA1, hampAll⟩ := exists_actual_complete_anchor_amplitudes α b c hα hb hpoint hc
  obtain ⟨βJ, hβJ, _, hjetAll⟩ := exists_actual_anchored_coefficient_jets α b hα hb hpoint
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  obtain ⟨βC, hβC, _, hcurAll⟩ := exists_actual_anchored_current_buffer (2 * Real.cos α) hS
  obtain ⟨Cb, H, AA, hCb, hH, hAA, hjacAll⟩ :=
    exists_actual_anchored_jacobian_majorant α b c hα hb hpoint hc
  let β := min βA (min βJ (min βC (min (Real.pi / 4) ((Real.pi - b - δB / 2) / 2))))
  have hgeom : 0 < Real.pi - b - δB / 2 := by linarith only [hleft, hδB]
  have hβ : 0 < β := by dsimp [β]; positivity
  have hbA : β ≤ βA := min_le_left _ _
  have hbJ : β ≤ βJ := (min_le_right _ _).trans (min_le_left _ _)
  have hbC : β ≤ βC := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbpi : β ≤ Real.pi / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbgap : β ≤ (Real.pi - b - δB / 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hβ1 : β ≤ 1 := hbA.trans hβA1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro ρ hρ hρβ hcut η hη hwidth hgap
  have hρπ : ρ ≤ Real.pi / 2 := (hρβ.trans hbpi).trans (by linarith only [Real.pi_pos])
  have hbρ : b + δB / 2 + ρ < Real.pi := by linarith only [hρβ, hbgap, hgeom]
  obtain ⟨δA, κ, A₀, hδA, _, hκ, hA₀, hamp⟩ := hampAll η hη
  obtain ⟨δJ, hδJ, _, hjets⟩ := hjetAll η hη
  obtain ⟨δC, hδC, _, hcur⟩ := hcurAll η hη
  obtain ⟨δM, hδM, _, hjac⟩ := hjacAll η hη hwidth
  let δ := min β (min δA (min δJ (min (δC / 8) δM)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdA : δ ≤ δA := (min_le_right _ _).trans (min_le_left _ _)
  have hdJ : δ ≤ δJ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC8 : δ ≤ δC / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdM : δ ≤ δM :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdC : δ ≤ δC := by linarith only [hdC8, hδC]
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, κ, hδ, hd1, hκ, ?_⟩
  intro j
  obtain ⟨Cj, hCj, ha⟩ := hamp j
  obtain ⟨Ag, Cg, hAg, hCg, hgj⟩ := actualLowerCompactAnchorCutoff_jets hρ η b δB j
  let A := Ag * Cj * AA
  let B := 2 * A₀ * Cg * max 1 H
  have hAg0 : 0 < Ag := zero_lt_one.trans_le hAg
  have hCg0 : 0 < Cg := zero_lt_one.trans_le hCg
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, B, by dsimp [A]; positivity, hB, ?_⟩
  intro n a σ hσ τ hτ μ ε hε
  let N := n + 2
  let g := actualLowerCompactAnchorCutoff η b δB ρ a
  let s := isotropicRadialParameter α ε
  let F : (Fin (n + 2) → ℝ) → ℂ := fun θ => anchoredTransportedDensity a σ η τ 1 g j (s, θ)
  let M := Ag * Cj * ‖isotropicParticleNormalization N‖ * (A₀ * Cg) ^ N *
    (N : ℝ) ^ anchorJetPolynomialOrder j * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)
  let E := M * (2 : ℝ) ^ N
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hgs (θ : Fin (n + 2) → ℝ) (hθ : θ ∈ tsupport g) : ∀ i, θ i ∈ Icc (-Real.pi - ρ) ρ := by
    have hh := compactLowerWindowProduct_weighted_tsupport hρ
      (actualLowerAnchorCutoff η b δB ρ a) hθ
    exact fun i => ⟨hh.1 i, hh.2 i⟩
  have hgsJ : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-Real.pi - βJ) βJ := by
    intro θ hθ i
    have hi := hgs θ hθ i
    exact ⟨by linarith only [hi.1, hρβ, hbJ], hi.2.trans (hρβ.trans hbJ)⟩
  have hgsC : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-Real.pi - βC) βC := by
    intro θ hθ i
    have hi := hgs θ hθ i
    exact ⟨by linarith only [hi.1, hρβ, hbC], hi.2.trans (hρβ.trans hbC)⟩
  have hg : ContDiff ℝ ∞ g := actualLowerCompactAnchorCutoff_contDiff η b δB ρ a
  have hrad := isotropicRadialParameter_estimates α ε hα hε.1 (hε.2.le.trans hd1)
  have hsnear : dist s ((2 * Real.cos α : ℝ) : ℂ) < δC :=
    hrad.2.2.2.2.trans_lt (by linarith only [hε.2, hdC8, hδC])
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun θ =>
    ((hcur (n + 2) (by omega) a σ hσ g hg hgsC τ 1
      ⟨hτ.1, hτ.2.trans hdC⟩ (by norm_num) s hrad.2.2.2.1 hsnear θ j).smooth.continuousAt.comp
      (f := fun x : Fin (n + 2) → ℝ => (s, x)) (continuousAt_const.prodMk continuousAt_id))
  have hFsupp : Function.support F ⊆ Icc (fun _ => -Real.pi - ρ) (fun _ => ρ) := by
    intro θ hθ
    have ht : θ ∈ tsupport g := anchoredTransportedDensity_tsupport a σ η τ 1 g j (subset_closure hθ)
    exact ⟨fun i => (hgs θ ht i).1, fun i => (hgs θ ht i).2⟩
  obtain ⟨hfcont, hf0, _, hfH, hJbound⟩ := hjac ε hε.1 (hε.2.le.trans hdM) ρ hρ.le hρπ
  have hFb (θ : Fin (n + 2) → ℝ) (_hθ : θ ∈ Icc (fun _ => -Real.pi - ρ) (fun _ => ρ)) :
      ‖F θ‖ ≤ E * AA * ∏ i ∈ Finset.univ.erase a, anchorJacobianWeight b Cb ε (θ i) := by
    by_cases ht : θ ∈ tsupport g
    · have hcos : c ≤ Real.cos b - Real.cos (θ a) :=
        actualLowerCompactAnchorCutoff_tsupport_cosine_gap hcut hη hρπ hgap hbρ a θ ht
      have hθA : ∀ i, θ i ∈ Icc (-Real.pi - βA) βA := fun i =>
        ⟨by linarith only [(hgs θ ht i).1, hρβ, hbA], (hgs θ ht i).2.trans (hρβ.trans hbA)⟩
      have ham := ha (n + 2) (by omega) a σ hσ Ag Cg hAg0.le hCg0.le g hg (hgj _ (by omega) a)
        ε hε.1 (hε.2.le.trans hdA) τ ⟨hτ.1, hτ.2.trans hdA⟩ θ hθA hcos
      have hjb := hJbound (n + 2) (by omega) a τ ⟨hτ.1, hτ.2.trans hdM⟩ θ (hgs θ ht) hcos
      change ‖actualCoordinateDeterminant η τ 1 (s, θ) * anchoredTransportDescendant a σ η τ 1 g j (s, θ)‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul hjb ham (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) hAA.le)
          (Finset.prod_nonneg (fun i _ => hf0 _)))).trans_eq (by dsimp [E]; ring)
    · have hz := (anchoredTransportedDensity_zero_germ a σ η τ 1 g j (s, θ) ht).eq_of_nhds
      change ‖anchoredTransportedDensity a σ η τ 1 g j (s, θ)‖ ≤ _
      rw [hz, norm_zero]
      exact mul_nonneg (mul_nonneg hE hAA.le) (Finset.prod_nonneg (fun i _ => hf0 _))
  have hint := named_anchor_product_integral_bound a μ (-Real.pi - ρ) ρ E AA H
    (by linarith [Real.pi_pos]) hE hAA.le F hF hFsupp (anchorJacobianWeight b Cb ε) hfcont hf0 hfH hFb
  have hjet := (hjets n a g hg hgsJ σ hσ τ 1 ⟨hτ.1, hτ.2.trans hdJ⟩ (by norm_num)
    μ j ε ⟨hε.1, hε.2.trans_le hdJ⟩).2
  rw [hjet]
  have hHpow : H ^ (n + 1) ≤ (max 1 H) ^ (n + 2) :=
    (pow_le_pow_left₀ hH.le (le_max_right _ _) (n + 1)).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  apply hint.2.2.trans
  apply (mul_le_mul_of_nonneg_left hHpow (mul_nonneg hE hAA.le)).trans_eq
  dsimp [E, M, A, B, N, rightGaussianCoefficientEnvelope]
  rw [isotropicParticleNormalization_norm]
  simp only [show n + 2 - 1 = n + 1 by omega, mul_pow, div_eq_mul_inv]
  ring

end IsingBulk.AnisoF002.Isotropic
