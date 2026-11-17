import IsingBulk.AnisoF002.C03.IsotropicRightShellCover

/-!
# A finite shell cover away from full coincidence

The positive diameter is imposed in the literal centered constraint
chart. The finite shell count depends on its fixed lower bound, never
on the radial parameter or on the angular mean. This construction
includes the two- and three-particle charts.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

def actualPositiveDiameterDomain (d : ℕ) (ρ b β r₀ : ℝ) : Set (Fin d → ℝ) :=
  {x | x ∈ actualCenteredRightDomain d ρ b β ∧
    ∃ i j, r₀ ≤ centeredConstraintAngles ρ x j - centeredConstraintAngles ρ x i}

theorem actualPositiveDiameterDomain_isCompact (d : ℕ) (ρ b β r₀ : ℝ) :
    IsCompact (actualPositiveDiameterDomain d ρ b β r₀) := by
  have he : actualPositiveDiameterDomain d ρ b β r₀ =
      actualCenteredRightDomain d ρ b β ∩
        ⋃ ij : Fin (d + 1) × Fin (d + 1),
          {x | r₀ ≤ centeredConstraintAngles ρ x ij.2 - centeredConstraintAngles ρ x ij.1} := by
    ext x
    simp only [actualPositiveDiameterDomain, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨hx, i, j, hij⟩
      exact ⟨hx, ⟨(i, j), hij⟩⟩
    · rintro ⟨hx, ⟨i, j⟩, hij⟩
      exact ⟨hx, i, j, hij⟩
  rw [he]
  apply (actualCenteredRightDomain_isCompact d ρ b β).inter_right
  exact isClosed_iUnion_of_finite fun ij => isClosed_le continuous_const
    (((continuous_apply ij.2).comp (centeredConstraintAngles_continuous ρ)).sub
      ((continuous_apply ij.1).comp (centeredConstraintAngles_continuous ρ)))

theorem dyadicRadius_antitone (R : ℝ) (hR : 0 ≤ R) : Antitone (dyadicRadius R) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hR (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

theorem exists_dyadicRadius_below {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ K : ℕ, dyadicRadius R K < r₀ / 2 := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := r₀ / (2 * R))
    (div_pos hr₀ (mul_pos (by norm_num) hR)) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨K, ?_⟩
  rw [div_pow, one_pow] at hK
  have hh := mul_lt_mul_of_pos_left hK hR
  change R / 2 ^ K < r₀ / 2
  convert hh using 1 <;> field_simp [ne_of_gt hR]

theorem actualPositiveDiameterDomain_subset_finite_shells {d K : ℕ}
    (ρ b β r₀ : ℝ) (hb : 0 < b) (hβ : 0 ≤ β) (hr₀ : 0 < r₀)
    (hK : dyadicRadius (b + 2 * β) K < r₀ / 2) :
    actualPositiveDiameterDomain d ρ b β r₀ ⊆
      ⋃ k : Fin K, actualCenteredShell d ρ b β (dyadicRadius (b + 2 * β) k) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hx0
    obtain ⟨i, j, hij⟩ := hx.2
    rw [hx0] at hij
    have hi : centeredConstraintAngles ρ (0 : Fin d → ℝ) i = ρ := by
      simp [centeredConstraintAngles]
    have hj : centeredConstraintAngles ρ (0 : Fin d → ℝ) j = ρ := by
      simp [centeredConstraintAngles]
    rw [hi, hj, sub_self] at hij
    exact (not_le_of_gt hr₀) hij
  have hu := actualCenteredRightDomain_subset_shells ρ b β hb hβ hx.1
  have hu' : x ∈ ⋃ k : ℕ, actualCenteredShell d ρ b β (dyadicRadius (b + 2 * β) k) :=
    hu.resolve_left (by simpa only [mem_singleton_iff] using hx0)
  obtain ⟨k, hk⟩ := mem_iUnion.mp hu'
  have hkK : k < K := by
    by_contra h
    have hle := dyadicRadius_antitone (b + 2 * β) (by positivity) (le_of_not_gt h)
    obtain ⟨i, j, hij⟩ := hx.2
    have hdiam := hk.2.2 i j
    linarith only [hle, hK, hij, hdiam]
  exact mem_iUnion.mpr ⟨⟨k, hkK⟩, hk⟩

theorem actualCenteredRightDomain_mean_bound {d : ℕ} {μ b β : ℝ}
    (hb : 0 ≤ b)
    (hne : (actualCenteredRightDomain d (μ - b) b β).Nonempty) :
    |μ| ≤ b + β := by
  obtain ⟨x, hx⟩ := hne
  have hlo := Finset.sum_le_sum
    (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx k).1)
  have hup := Finset.sum_le_sum
    (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx k).2)
  rw [centeredConstraintAngles_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hlo hup
  have hN : (0 : ℝ) < d + 1 := by positivity
  have hlow : -β ≤ μ := by
    have : (d + 1 : ℝ) * (-b - β) ≤ (d + 1 : ℝ) * (μ - b) := by exact_mod_cast hlo
    nlinarith only [this, hN]
  have hhigh : μ ≤ b + β := by
    have : (d + 1 : ℝ) * (μ - b) ≤ (d + 1 : ℝ) * β := by exact_mod_cast hup
    nlinarith only [this, hN]
  exact abs_le.mpr ⟨by linarith only [hlow, hb], hhigh⟩

end IsingBulk.AnisoF002.Isotropic
