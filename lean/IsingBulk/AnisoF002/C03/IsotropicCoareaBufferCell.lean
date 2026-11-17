import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferFiberMeasure
import IsingBulk.AnisoF002.C03.IsotropicExtremeCellCoarea

/-!
# Full-dimensional actual cell coarea with geometry before η
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_extreme_cell_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r γ : ℝ, 0 < r →
        (∫ p in actualExtremeCell n ((n + 2 : ℝ) * (μ - b)) b β r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
            (extremeFiberAngles ((n + 2 : ℝ) * (μ - b)) p)) ≤
          (C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_full_density_fiber_setIntegral_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, W, hδ, hδβ, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r γ hr
  let s := isotropicRadialParameter α ε
  let a := (n + 2 : ℝ) * (μ - b)
  let K := C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  let I := fun y : Fin n → ℝ =>
    ∫ t in fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b β r,
      actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a (t, y))
  let P := fun y : Fin n → ℝ => ∏ k, W * branchWeight ε (y k + b)
  have hI : Integrable I volume :=
    actualExtremeCell_fiberIntegral_integrable n a b β r s hs η τ ξ γ hη hτ.1 hξ.1
  have hP : Continuous P := by
    apply continuous_finsetProd
    intro k _
    exact continuous_const.mul ((branchWeight_continuous hε).comp ((continuous_apply k).add continuous_const))
  have hpint : IntegrableOn (fun y => K * P y) (remainingAngularBox n μ b r) volume :=
    (continuous_const.mul hP).integrableOn_Icc
  have hpointwise (y : Fin n → ℝ) : I y ≤ K * P y := by
    have hh := hbound (n + 2) (by omega) ε hε hεδ τ ξ hτ hξ (extremeFiberBase a y)
      0 (Fin.last (n + 1)) (Fin.ne_of_val_ne (by simp)) r γ hr
    rw [extremeFiberBase_remaining_weight a W ε b hW hε y] at hh
    dsimp only [a] at hh
    rw [extremeFiberBase_shifted_mean] at hh
    simpa only [I, K, P, s, a, extremeFiberAngles, Nat.cast_add, Nat.cast_ofNat] using hh
  rw [actualExtremeCell_integral_fubini_box n μ b β r s hs η τ ξ γ hη hτ.1 hξ.1]
  change (∫ y in remainingAngularBox n μ b r, I y) ≤ K * _
  calc
    _ ≤ ∫ y in remainingAngularBox n μ b r, K * P y :=
      setIntegral_mono_on hI.integrableOn hpint measurableSet_Icc (fun y _ => hpointwise y)
    _ = K * ∫ y in remainingAngularBox n μ b r, P y := integral_const_mul K P
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (remaining_branch_weight_product_integral_bound n W ε μ b r hW.le hε hr) hK

end IsingBulk.AnisoF002.Isotropic
