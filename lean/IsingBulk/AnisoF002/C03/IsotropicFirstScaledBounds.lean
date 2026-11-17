import IsingBulk.AnisoF002.C03.IsotropicFirstPhysicalJets
import IsingBulk.AnisoF002.C03.IsotropicFirstPointwiseLimit
import IsingBulk.AnisoF002.C03.RegularScaledCollision

/-!
# Actual isotropic scaled jets and the complete Vandermonde majorant

The radial path, full physical density, zero-sum constraint and every
Vandermonde factor are unchanged. These estimates are for fixed particle
number and the full original independent-coordinate first chart.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstRealScaledJet {N : ℕ} (α : ℝ) (σ : ℂ) (j : ℕ) (s : ℝ)
    (x : Fin N → ℝ) : ℂ :=
  ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * N.choose 2)) *
    iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
      (h, fun i => ((s * x i : ℝ) : ℂ)))
      (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ))

def isotropicFirstLeadingJet {N : ℕ} (α : ℝ) (j : ℕ) (x : Fin N → ℝ) : ℂ :=
  (edgeVandermondeSquared (complexAngles x) * isotropicFirstCenterAmplitude N α) *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ) *
      (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) ^ j /
      (2 * (N : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) *
        ∑ i, (x i : ℂ) ^ 2) ^ (j + 1))

theorem isotropicFirstRealScaledJet_limit {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℝ) (hx : ∑ i, x i = 0) (j : ℕ) :
    Tendsto (fun s : ℝ => isotropicFirstRealScaledJet α σ j s x) (𝓝[>] (0 : ℝ))
      (𝓝 (isotropicFirstLeadingJet α j x)) := by
  have hcast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hl := (isotropic_first_actual_scaled_jet_limit hN hα hπ σ hres x hx j).comp hcast
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [isotropicFirstRealScaledJet, Function.comp_def, Complex.ofReal_mul,
    isotropicRadialParameter_filled α (s ^ 2) (by positivity), Complex.ofReal_pow]

theorem exists_isotropic_first_full_density_jet_bound {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1) (j : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ e : ℝ, 0 < e →
      ∀ u : Fin N → ℝ, (∑ i, u i) = 0 → e + angularQuadratic u < δ →
      ‖iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, complexAngles u)) (isotropicRadialParameter α e - (2 * Real.cos α : ℂ))‖ ≤
          C * ‖edgeVandermondeSquared (complexAngles u)‖ / (e + angularQuadratic u) ^ (j + 1) := by
  obtain ⟨δ, C, hδ, hC, hh⟩ := exists_isotropic_first_actual_quotient_jet_bound hN hα hhalf σ hres j
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro e he u hu hsmall
  have hf : (fun h => isotropicFirstJointDensity α σ (h, complexAngles u)) =
      fun h => edgeVandermondeSquared (complexAngles u) *
        isotropicFirstUnscaledRatio α σ (h, complexAngles u) := by
    funext h
    rw [isotropicFirstJointDensity, isotropicFirstDensity_exact]
    unfold isotropicFirstUnscaledRatio
    ring
  rw [hf, iteratedDeriv_const_mul_field, norm_mul]
  have hb := mul_le_mul_of_nonneg_left (hh e he u hu hsmall)
    (norm_nonneg (edgeVandermondeSquared (complexAngles u)))
  change ‖edgeVandermondeSquared (complexAngles u)‖ *
    ‖iteratedDeriv j (fun h => isotropicFirstUnscaledRatio α σ (h, fun i => (u i : ℂ)))
      (isotropicRadialParameter α e - (2 * Real.cos α : ℂ))‖ ≤ _
  apply hb.trans_eq
  unfold angularQuadratic
  ring

theorem exists_isotropic_first_scaled_jet_majorant {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1) (j : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ s : ℝ, 0 < s →
      ∀ x : Fin N → ℝ, (∑ i, x i) = 0 →
        s ^ 2 + angularQuadratic (fun i => s * x i) < δ →
        ‖isotropicFirstRealScaledJet α σ j s x‖ ≤
          C * ‖edgeVandermondeSquared (complexAngles x)‖ / (1 + angularQuadratic x) ^ (j + 1) := by
  obtain ⟨δ, C, hδ, hC, hh⟩ := exists_isotropic_first_full_density_jet_bound hN hα hhalf σ hres j
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro s hs x hx hsmall
  have hsum : ∑ i, s * x i = 0 := by rw [← Finset.mul_sum, hx, mul_zero]
  have hb := hh (s ^ 2) (sq_pos_of_pos hs) (fun i => s * x i) hsum hsmall
  have hV : edgeVandermondeSquared (complexAngles (fun i => s * x i)) =
      (s : ℂ) ^ (2 * N.choose 2) * edgeVandermondeSquared (complexAngles x) := by
    have he : complexAngles (fun i => s * x i) = fun i => (s : ℂ) * complexAngles x i := by
      funext i
      exact Complex.ofReal_mul s (x i)
    rw [he, edgeVandermondeSquared_scaling]
  have hden : s ^ 2 + angularQuadratic (fun i => s * x i) =
      s ^ 2 * (1 + angularQuadratic x) := by rw [angularQuadratic_mul]; ring
  rw [hV, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le, hden] at hb
  unfold isotropicFirstRealScaledJet
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have he := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ s ^ (2 * j + 2) / s ^ (2 * N.choose 2) by positivity)
  apply he.trans_eq
  rw [show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul, mul_pow]
  field_simp

end
end IsingBulk.AnisoF002.Isotropic
