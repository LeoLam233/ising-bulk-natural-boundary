import IsingBulk.AnisoF002.C03.IsotropicShellScaleBound
import IsingBulk.AnisoF002.C03.IsotropicDyadicShells

/-!
# The dyadic shells cover the full real right chart

The full coincidence is the single origin of the centered constraint
chart. Every other point in the exact right rectangle belongs to one
of the actual diameter shells. The largest radius is fixed, with no
parameter-dependent subdivision or omitted particle range.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric MeasureTheory

def actualCenteredRightDomain (d : ℕ) (ρ b δ : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ k, centeredConstraintAngles ρ x k ∈ Icc (-b - δ) δ}

theorem actualCenteredRightDomain_isClosed (d : ℕ) (ρ b δ : ℝ) :
    IsClosed (actualCenteredRightDomain d ρ b δ) := by
  have he : actualCenteredRightDomain d ρ b δ =
      ⋂ k : Fin (d + 1), (fun x => centeredConstraintAngles ρ x k) ⁻¹' Icc (-b - δ) δ := by
    ext x
    simp only [actualCenteredRightDomain, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun k => isClosed_Icc.preimage
    ((continuous_apply k).comp (centeredConstraintAngles_continuous ρ))

theorem actualCenteredRightDomain_isCompact (d : ℕ) (ρ b δ : ℝ) :
    IsCompact (actualCenteredRightDomain d ρ b δ) := by
  apply isCompact_Icc.of_isClosed_subset (actualCenteredRightDomain_isClosed d ρ b δ)
    (s := Icc (fun _ : Fin d => -b - δ - ρ) (fun _ => δ - ρ))
  intro x hx
  have hk (k : Fin d) := hx k.castSucc
  simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hk
  exact ⟨fun k => by linarith only [(hk k).1], fun k => by linarith only [(hk k).2]⟩

theorem centeredConstraintAngles_constant_iff {d : ℕ} (ρ c : ℝ) (x : Fin d → ℝ)
    (hc : ∀ i, centeredConstraintAngles ρ x i = c) : x = 0 := by
  have hs := centeredConstraintAngles_sum ρ x
  simp_rw [hc] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hN : (d + 1 : ℝ) ≠ 0 := by positivity
  have hρ : c = ρ := by
    have hh : (d + 1 : ℝ) * c = (d + 1 : ℝ) * ρ := by exact_mod_cast hs
    exact mul_left_cancel₀ hN hh
  funext i
  have hi := hc i.castSucc
  simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc, hρ] at hi
  change x i = 0
  linarith only [hi]

theorem exists_dyadicRadius_cover (R d : ℝ) (hR : 0 < R) (hd : 0 < d) (hdR : d ≤ 2 * R) :
    ∃ k : ℕ, dyadicRadius R k ≤ d ∧ d ≤ 2 * dyadicRadius R k := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hd (mul_pos (by norm_num) hR)) ((div_le_one (by positivity)).mpr hdR)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  have hh : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [div_pow, one_pow]
  rw [pow_succ, hh] at hk
  rw [hh] at hk'
  refine ⟨k, ?_, ?_⟩
  · have h := (lt_div_iff₀ (by positivity : 0 < 2 * R)).mp hk
    change R / 2 ^ k ≤ d
    have he : (1 / 2 ^ k * (1 / 2) : ℝ) * (2 * R) = R / 2 ^ k := by ring
    rw [he] at h
    exact h.le
  · have h := (div_le_iff₀ (by positivity : 0 < 2 * R)).mp hk'
    change d ≤ 2 * (R / 2 ^ k)
    convert h using 1
    ring

theorem actualCenteredRightDomain_subset_shells {d : ℕ} (ρ b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) :
    actualCenteredRightDomain d ρ b δ ⊆ {0} ∪
      ⋃ k : ℕ, actualCenteredShell d ρ b δ (dyadicRadius (b + 2 * δ) k) := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl (mem_singleton_iff.mpr hx0)
  · apply Or.inr
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
      (centeredConstraintAngles ρ x) Finset.univ_nonempty
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (centeredConstraintAngles ρ x) Finset.univ_nonempty
    have hg : 0 < centeredConstraintAngles ρ x j - centeredConstraintAngles ρ x i := by
      by_contra h
      have hle := le_of_not_gt h
      apply hx0
      apply centeredConstraintAngles_constant_iff ρ (centeredConstraintAngles ρ x i) x
      intro k
      linarith only [hi k (Finset.mem_univ k), hj k (Finset.mem_univ k), hle]
    have hR : 0 < b + 2 * δ := by positivity
    have hdiam : centeredConstraintAngles ρ x j - centeredConstraintAngles ρ x i ≤
        2 * (b + 2 * δ) := by
      linarith only [(hx j).2, (hx i).1, hb, hδ]
    obtain ⟨k, hk, hk'⟩ := exists_dyadicRadius_cover (b + 2 * δ) _ hR hg hdiam
    apply mem_iUnion.mpr
    refine ⟨k, hx, ⟨i, j, hk⟩, ?_⟩
    intro l m
    linarith only [hi l (Finset.mem_univ l), hj m (Finset.mem_univ m), hk']

end IsingBulk.AnisoF002.Isotropic
