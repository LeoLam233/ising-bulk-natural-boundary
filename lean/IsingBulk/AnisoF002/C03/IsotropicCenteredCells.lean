import IsingBulk.AnisoF002.C03.IsotropicExtremeCellCoarea
import Mathlib.Logic.Equiv.Fintype

/-!
# Exact centered charts for every ordered extreme cell

The constrained mean is arbitrary. Particle permutations preserve its
literal independent Lebesgue coordinates, and the first/last fiber
chart is an explicit measure-preserving translation of Fin.cons.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def extremeAngleRegion {N : ℕ} (i j : Fin N) (b δ r : ℝ) : Set (Fin N → ℝ) :=
  {θ | (∀ k, θ k ∈ Icc (-b - δ) δ) ∧ (∀ k, θ i ≤ θ k) ∧ (∀ k, θ k ≤ θ j) ∧
    r ≤ θ j - θ i ∧ θ j - θ i ≤ 2 * r}

theorem extremeAngleRegion_isClosed {N : ℕ} (i j : Fin N) (b δ r : ℝ) :
    IsClosed (extremeAngleRegion i j b δ r) := by
  unfold extremeAngleRegion
  simp only [mem_Icc, ofPred_and, ofPred_forall]
  exact (isClosed_iInter (fun k => (isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_le (continuous_apply k) continuous_const))).inter
    ((isClosed_iInter (fun k => isClosed_le (continuous_apply i) (continuous_apply k))).inter
      ((isClosed_iInter (fun k => isClosed_le (continuous_apply k) (continuous_apply j))).inter
        ((isClosed_le continuous_const ((continuous_apply j).sub (continuous_apply i))).inter
          (isClosed_le ((continuous_apply j).sub (continuous_apply i)) continuous_const))))

theorem extremeAngleRegion_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N)
    (b δ r : ℝ) (θ : Fin N → ℝ) :
    (fun k => θ (σ k)) ∈ extremeAngleRegion i j b δ r ↔
      θ ∈ extremeAngleRegion (σ i) (σ j) b δ r := by
  constructor
  · rintro ⟨ha, hb, hc, hd, he⟩
    refine ⟨?_, ?_, ?_, hd, he⟩
    · intro k
      simpa only [Equiv.apply_symm_apply] using ha (σ.symm k)
    · intro k
      simpa only [Equiv.apply_symm_apply] using hb (σ.symm k)
    · intro k
      simpa only [Equiv.apply_symm_apply] using hc (σ.symm k)
  · rintro ⟨ha, hb, hc, hd, he⟩
    exact ⟨fun k => ha (σ k), fun k => hb (σ k), fun k => hc (σ k), hd, he⟩

theorem centeredConstraintAngles_continuous {d : ℕ} (ρ : ℝ) :
    Continuous (centeredConstraintAngles (d := d) ρ) := by
  rw [show centeredConstraintAngles (d := d) ρ = (fun x : Fin d → ℝ =>
    Fin.snoc (fun i => ρ + x i) ((d + 1 : ℝ) * ρ - ∑ i, (ρ + x i)))
    from funext (centeredConstraintAngles_eq_snoc ρ)]
  apply Continuous.finSnoc (A := fun _ : Fin (d + 1) => ℝ)
  · exact continuous_pi (fun i => continuous_const.add (continuous_apply i))
  · exact continuous_const.sub (continuous_finsetSum _
      (fun i _ => continuous_const.add (continuous_apply i)))

def centeredExtremeCell {d : ℕ} (ρ b δ r : ℝ) (i j : Fin (d + 1)) : Set (Fin d → ℝ) :=
  centeredConstraintAngles ρ ⁻¹' extremeAngleRegion i j b δ r

theorem centeredExtremeCell_isClosed {d : ℕ} (ρ b δ r : ℝ) (i j : Fin (d + 1)) :
    IsClosed (centeredExtremeCell ρ b δ r i j) :=
  (extremeAngleRegion_isClosed i j b δ r).preimage (centeredConstraintAngles_continuous ρ)

theorem centeredExtremeCell_isCompact {d : ℕ} (ρ b δ r : ℝ) (i j : Fin (d + 1)) :
    IsCompact (centeredExtremeCell ρ b δ r i j) := by
  apply isCompact_Icc.of_isClosed_subset (centeredExtremeCell_isClosed ρ b δ r i j)
    (s := Icc (fun _ : Fin d => -b - δ - ρ) (fun _ => δ - ρ))
  intro x hx
  have hk (k : Fin d) := hx.1 k.castSucc
  simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hk
  exact ⟨fun k => by linarith only [(hk k).1], fun k => by linarith only [(hk k).2]⟩

theorem centeredExtremeCell_chartPermutation {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (ρ b δ r : ℝ) (i j : Fin (d + 1)) (x : Fin d → ℝ) :
    constrainedChartPermutation σ x ∈ centeredExtremeCell ρ b δ r i j ↔
      x ∈ centeredExtremeCell ρ b δ r (σ i) (σ j) := by
  change centeredConstraintAngles ρ (constrainedChartPermutation σ x) ∈ extremeAngleRegion i j b δ r ↔ _
  rw [centeredConstraintAngles_chartPermutation, extremeAngleRegion_perm]
  rfl

theorem centeredExtremeCell_permutation_integral {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (ρ b δ r : ℝ) (i j : Fin (d + 1)) (s : ℂ) (η τ ξ γ : ℝ) :
    (∫ x in centeredExtremeCell ρ b δ r (σ i) (σ j),
      actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)) =
      ∫ x in centeredExtremeCell ρ b δ r i j,
        actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x) := by
  let f := fun x : Fin d → ℝ => actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)
  let S := centeredExtremeCell ρ b δ r i j
  let T := centeredExtremeCell ρ b δ r (σ i) (σ j)
  have he : (fun x => S.indicator f (constrainedChartPermutation σ x)) = T.indicator f := by
    funext x
    have hm := centeredExtremeCell_chartPermutation σ ρ b δ r i j x
    have hf := actualFullPhaseDensity_centered_chart_invariant σ s η τ ξ γ ρ x
    by_cases hx : x ∈ T
    · have hh : constrainedChartPermutation σ x ∈ S := hm.mpr hx
      simp only [indicator_of_mem hx, indicator_of_mem hh]
      exact hf
    · have hh : constrainedChartPermutation σ x ∉ S := fun h => hx (hm.mp h)
      simp only [indicator_of_notMem hx, indicator_of_notMem hh]
  rw [← integral_indicator (centeredExtremeCell_isClosed ρ b δ r (σ i) (σ j)).measurableSet,
    ← integral_indicator (centeredExtremeCell_isClosed ρ b δ r i j).measurableSet]
  have hh := constrainedChartPermutation_integral σ (S.indicator f)
  rw [he] at hh
  exact hh

def centeredParameterChart (n : ℕ) (ρ : ℝ) : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.trans
    (MeasurableEquiv.addRight (fun _ => -ρ))

theorem centeredParameterChart_apply (n : ℕ) (ρ : ℝ) (p : ℝ × (Fin n → ℝ)) :
    centeredParameterChart n ρ p = fun k => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) k - ρ := by
  funext k
  simp only [centeredParameterChart, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_addRight,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq, Pi.add_apply, sub_eq_add_neg]

theorem centeredParameterChart_measurePreserving (n : ℕ) (ρ : ℝ) :
    MeasurePreserving (centeredParameterChart n ρ) volume volume :=
  (measurePreserving_add_right volume (fun _ : Fin (n + 1) => -ρ)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

theorem centeredParameterChart_angles (n : ℕ) (ρ : ℝ) (p : ℝ × (Fin n → ℝ)) :
    centeredConstraintAngles ρ (centeredParameterChart n ρ p) =
      extremeFiberAngles ((n + 2 : ℝ) * ρ) p := by
  rw [centeredConstraintAngles_eq_snoc, extremeFiberAngles_eq_snoc]
  have hf : (fun i => ρ + centeredParameterChart n ρ p i) = Fin.cons p.1 p.2 := by
    funext i
    rw [centeredParameterChart_apply]
    ring
  rw [hf, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  push_cast
  ring

theorem centeredParameterChart_cell (n : ℕ) (ρ b δ r : ℝ) (p : ℝ × (Fin n → ℝ)) :
    centeredParameterChart n ρ p ∈ centeredExtremeCell ρ b δ r 0 (Fin.last (n + 1)) ↔
      p ∈ actualExtremeCell n ((n + 2 : ℝ) * ρ) b δ r := by
  change centeredConstraintAngles ρ (centeredParameterChart n ρ p) ∈
    extremeAngleRegion 0 (Fin.last (n + 1)) b δ r ↔ _
  rw [centeredParameterChart_angles]
  simp only [extremeAngleRegion, mem_ofPred_eq, extremeFiberAngles, actualExtremeCell,
    fullExtremeFiber, positiveExtremeFiber, neg_add_rev]
  ring_nf

theorem centeredParameterChart_cell_integral (n : ℕ) (ρ b δ r : ℝ)
    (s : ℂ) (η τ ξ γ : ℝ) :
    (∫ x in centeredExtremeCell ρ b δ r 0 (Fin.last (n + 1)),
      actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)) =
      ∫ p in actualExtremeCell n ((n + 2 : ℝ) * ρ) b δ r,
        actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles ((n + 2 : ℝ) * ρ) p) := by
  let S := centeredExtremeCell ρ b δ r 0 (Fin.last (n + 1))
  let T := actualExtremeCell n ((n + 2 : ℝ) * ρ) b δ r
  let f := fun x : Fin (n + 1) → ℝ => actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles ρ x)
  let g := fun p : ℝ × (Fin n → ℝ) => actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles ((n + 2 : ℝ) * ρ) p)
  have he : (fun p => S.indicator f (centeredParameterChart n ρ p)) = T.indicator g := by
    funext p
    have hm := centeredParameterChart_cell n ρ b δ r p
    by_cases hp : p ∈ T
    · have hh : centeredParameterChart n ρ p ∈ S := hm.mpr hp
      simp only [indicator_of_mem hp, indicator_of_mem hh, f, g, centeredParameterChart_angles]
    · have hh : centeredParameterChart n ρ p ∉ S := fun h => hp (hm.mp h)
      simp only [indicator_of_notMem hp, indicator_of_notMem hh]
  rw [← integral_indicator (centeredExtremeCell_isClosed ρ b δ r 0 (Fin.last (n + 1))).measurableSet,
    ← integral_indicator (actualExtremeCell_isClosed n ((n + 2 : ℝ) * ρ) b δ r).measurableSet]
  exact ((centeredParameterChart_measurePreserving n ρ).integral_comp'
    (f := centeredParameterChart n ρ) (S.indicator f)).symm.trans (by rw [he])

end IsingBulk.AnisoF002.Isotropic
