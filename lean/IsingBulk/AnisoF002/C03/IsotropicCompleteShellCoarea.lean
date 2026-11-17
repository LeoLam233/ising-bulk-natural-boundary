import IsingBulk.AnisoF002.C03.IsotropicCenteredCells

/-!
# Complete fixed-mean right-shell coarea

Every ordered extreme cell is carried to the proved first/last cell
by a genuine measure-preserving constrained permutation. Their finite
cover is the entire diameter shell, including all population values.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem exists_perm_first_last (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), σ 0 = i ∧ σ (Fin.last (n + 1)) = j := by
  let f : Bool → Fin (n + 2) := fun q => if q then 0 else Fin.last (n + 1)
  let g : Bool → Fin (n + 2) := fun q => if q then i else j
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f]
  have hg : Function.Injective g := by
    intro a b hab
    cases a <;> cases b <;> simp_all [g, Ne.symm hij]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, by simpa [f, g] using hσ true, by simpa [f, g] using hσ false⟩

def actualCenteredShell (d : ℕ) (ρ b δ r : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ k, centeredConstraintAngles ρ x k ∈ Icc (-b - δ) δ) ∧
    (∃ i j, r ≤ centeredConstraintAngles ρ x j - centeredConstraintAngles ρ x i) ∧
    (∀ i j, centeredConstraintAngles ρ x j - centeredConstraintAngles ρ x i ≤ 2 * r)}

theorem actualCenteredShell_eq_union (d : ℕ) (ρ b δ r : ℝ) :
    actualCenteredShell d ρ b δ r = ⋃ ij : Fin (d + 1) × Fin (d + 1),
      centeredExtremeCell ρ b δ r ij.1 ij.2 := by
  ext x
  constructor
  · rintro ⟨hrect, ⟨k, l, hkl⟩, hdiam⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
      (centeredConstraintAngles ρ x) Finset.univ_nonempty
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (centeredConstraintAngles ρ x) Finset.univ_nonempty
    apply mem_iUnion.mpr
    refine ⟨(i, j), hrect, (fun a => hi a (Finset.mem_univ a)),
      (fun a => hj a (Finset.mem_univ a)), ?_, hdiam i j⟩
    linarith only [hi k (Finset.mem_univ k), hj l (Finset.mem_univ l), hkl]
  · intro hx
    obtain ⟨⟨i, j⟩, hrect, hmin, hmax, hlow, hupp⟩ := mem_iUnion.mp hx
    refine ⟨hrect, ⟨i, j, hlow⟩, ?_⟩
    intro k l
    linarith only [hmin k, hmax l, hupp]

theorem actualCenteredShell_isCompact (d : ℕ) (ρ b δ r : ℝ) :
    IsCompact (actualCenteredShell d ρ b δ r) := by
  rw [actualCenteredShell_eq_union]
  exact isCompact_iUnion (fun ij => centeredExtremeCell_isCompact ρ b δ r ij.1 ij.2)

theorem centeredExtremeCell_diagonal_empty {d : ℕ} (ρ b δ r : ℝ) (hr : 0 < r)
    (i : Fin (d + 1)) : centeredExtremeCell ρ b δ r i i = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hh := hx.2.2.2.1
  linarith only [hh, hr]

theorem actualCenteredShell_integral_le_cells (d : ℕ) (ρ b δ r : ℝ)
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    (∫ x in actualCenteredShell d ρ b δ r,
      actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)) ≤
      ∑ ij : Fin (d + 1) × Fin (d + 1),
        ∫ x in centeredExtremeCell ρ b δ r ij.1 ij.2,
          actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x) := by
  let f := fun x : Fin d → ℝ => actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)
  let S := actualCenteredShell d ρ b δ r
  let T := fun ij : Fin (d + 1) × Fin (d + 1) => centeredExtremeCell ρ b δ r ij.1 ij.2
  have hf : Continuous f := (actualFullPhaseDensity_angles_continuous s hs η τ ξ γ hη hτ hξ 0).comp
    (centeredConstraintAngles_continuous ρ)
  have hS := actualCenteredShell_isCompact d ρ b δ r
  have hT (ij : Fin (d + 1) × Fin (d + 1)) := centeredExtremeCell_isCompact ρ b δ r ij.1 ij.2
  have hSI : Integrable (S.indicator f) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hf.continuousOn.integrableOn_compact hS)
  have hTI (ij) : Integrable ((T ij).indicator f) volume :=
    (integrable_indicator_iff (hT ij).measurableSet).mpr (hf.continuousOn.integrableOn_compact (hT ij))
  have hnonneg (ij) (x) : 0 ≤ (T ij).indicator f x := by
    apply indicator_nonneg
    intro _ _
    exact actualFullPhaseDensity_nonneg _ _ _ _ _ _
  have hpt (x : Fin d → ℝ) : S.indicator f x ≤ ∑ ij, (T ij).indicator f x := by
    by_cases hx : x ∈ S
    · have hu : x ∈ ⋃ ij, T ij := by simpa only [S, actualCenteredShell_eq_union, T] using hx
      obtain ⟨ij, hij⟩ := mem_iUnion.mp hu
      rw [indicator_of_mem hx]
      calc
        f x = (T ij).indicator f x := (indicator_of_mem hij f).symm
        _ ≤ _ := Finset.single_le_sum (fun kl _ => hnonneg kl x) (Finset.mem_univ ij)
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun ij _ => hnonneg ij x)
  have hh := integral_mono hSI (integrable_finsetSum Finset.univ (fun ij _ => hTI ij)) hpt
  rw [integral_finsetSum Finset.univ (fun ij _ => hTI ij)] at hh
  rw [integral_indicator hS.measurableSet] at hh
  have he (ij : Fin (d + 1) × Fin (d + 1)) :
      (∫ x, (T ij).indicator f x) = ∫ x in T ij, f x :=
    integral_indicator (hT ij).measurableSet
  simp_rw [he] at hh
  exact hh

/-- Complete frozen right-shell coarea in literal independent centered
Lebesgue coordinates. The extrema cover contributes only N squared. -/
theorem exists_actual_complete_shell_coarea (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r γ : ℝ, 0 < r →
        (∫ x in actualCenteredShell (n + 1) (μ - b) b δ r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
            (centeredConstraintAngles (μ - b) x)) ≤
          (C * (n + 2) ^ 3 * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨δ, C, W, hδ, hδ1, hC, hW, hbound⟩ :=
    exists_actual_extreme_cell_coarea α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, W, hδ, hδ1, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r γ hr
  let s := isotropicRadialParameter α ε
  let B := (C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
    (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hcell (i j : Fin (n + 2)) :
      (∫ x in centeredExtremeCell (μ - b) b δ r i j,
        actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles (μ - b) x)) ≤ B := by
    by_cases hij : i = j
    · subst j
      rw [centeredExtremeCell_diagonal_empty _ _ _ _ hr, Measure.restrict_empty, integral_zero_measure]
      exact hB
    · obtain ⟨σ, hσ0, hσlast⟩ := exists_perm_first_last n i j hij
      rw [← hσ0, ← hσlast, centeredExtremeCell_permutation_integral σ,
        centeredParameterChart_cell_integral]
      exact hbound n ε hε hεδ τ ξ hτ hξ μ r γ hr
  have hmain := (actualCenteredShell_integral_le_cells (n + 1) (μ - b) b δ r s hs η τ ξ γ hη hτ.1 hξ.1).trans
    (Finset.sum_le_sum (fun ij _ => hcell ij.1 ij.2))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmain
  exact hmain.trans_eq (by dsimp [B]; ring)

end IsingBulk.AnisoF002.Isotropic
