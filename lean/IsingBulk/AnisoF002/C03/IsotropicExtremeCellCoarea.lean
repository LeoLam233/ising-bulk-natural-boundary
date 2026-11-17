import IsingBulk.AnisoF002.C03.IsotropicExtremeCellGeometry

/-!
# Full-dimensional physical coarea on an actual extreme cell

The exact original graph-coordinate Lebesgue measure is disintegrated
along the genuine extreme fiber. Joint compact-cell integrability is
proved first. The two actual extreme factors are then integrated before
the remaining independent branch-weight envelopes.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem actualExtremeCell_indicator_slice (n : ℕ) (a b δ r : ℝ)
    (f : (ℝ × (Fin n → ℝ)) → ℝ) (y : Fin n → ℝ) :
    (∫ t : ℝ, (actualExtremeCell n a b δ r).indicator f (t, y)) =
      ∫ t in fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b δ r, f (t, y) := by
  have he : (fun t : ℝ => (actualExtremeCell n a b δ r).indicator f (t, y)) =
      (fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b δ r).indicator
        (fun t => f (t, y)) := rfl
  rw [he, integral_indicator]
  exact (positiveExtremeFiber_isClosed (extremeFiberBase a y) 0 (Fin.last (n + 1)) (b + δ) δ r).measurableSet

theorem actualExtremeCell_fiberIntegral_integrable (n : ℕ) (a b δ r : ℝ)
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    Integrable (fun y : Fin n → ℝ =>
      ∫ t in fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b δ r,
        actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a (t, y))) volume := by
  let f := fun p : ℝ × (Fin n → ℝ) => actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a p)
  have hI : Integrable ((actualExtremeCell n a b δ r).indicator f) (volume.prod volume) :=
    (integrable_indicator_iff (actualExtremeCell_isClosed n a b δ r).measurableSet).mpr
      (actualExtremeCell_density_integrable n a b δ r s hs η τ ξ γ hη hτ hξ)
  have hh := hI.integral_prod_right
  simp_rw [actualExtremeCell_indicator_slice] at hh
  exact hh

theorem actualExtremeCell_integral_fubini (n : ℕ) (a b δ r : ℝ)
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    (∫ p in actualExtremeCell n a b δ r,
      actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a p)) =
      ∫ y : Fin n → ℝ, ∫ t in fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b δ r,
        actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a (t, y)) := by
  let f := fun p : ℝ × (Fin n → ℝ) => actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a p)
  have hI : Integrable ((actualExtremeCell n a b δ r).indicator f) (volume.prod volume) :=
    (integrable_indicator_iff (actualExtremeCell_isClosed n a b δ r).measurableSet).mpr
      (actualExtremeCell_density_integrable n a b δ r s hs η τ ξ γ hη hτ hξ)
  rw [← integral_indicator (actualExtremeCell_isClosed n a b δ r).measurableSet]
  change (∫ p, (actualExtremeCell n a b δ r).indicator f p ∂volume.prod volume) = _
  rw [integral_prod_symm _ hI]
  simp_rw [actualExtremeCell_indicator_slice]
  rfl

theorem actualExtremeCell_empty_fiber_off_box (n : ℕ) (μ b δ r : ℝ)
    (y : Fin n → ℝ) (hy : y ∉ remainingAngularBox n μ b r) :
    fullExtremeFiber (extremeFiberBase ((n + 2 : ℝ) * (μ - b)) y) 0 (Fin.last (n + 1)) b δ r = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨t, ht⟩
  exact hy (actualExtremeCell_remaining_mem μ b δ r (t, y) ht)

theorem actualExtremeCell_integral_fubini_box (n : ℕ) (μ b δ r : ℝ)
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    (∫ p in actualExtremeCell n ((n + 2 : ℝ) * (μ - b)) b δ r,
      actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles ((n + 2 : ℝ) * (μ - b)) p)) =
      ∫ y in remainingAngularBox n μ b r,
        ∫ t in fullExtremeFiber (extremeFiberBase ((n + 2 : ℝ) * (μ - b)) y) 0 (Fin.last (n + 1)) b δ r,
          actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles ((n + 2 : ℝ) * (μ - b)) (t, y)) := by
  rw [actualExtremeCell_integral_fubini n _ b δ r s hs η τ ξ γ hη hτ hξ]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [actualExtremeCell_empty_fiber_off_box n μ b δ r y hy, Measure.restrict_empty, integral_zero_measure]

/-- The actual full N-dimensional constrained density on a fixed ordered
extreme cell, including every physical Jacobian and the complete product
denominator. Constants are fixed before particle number and mean. -/
theorem exists_actual_extreme_cell_coarea (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r γ : ℝ, 0 < r →
        (∫ p in actualExtremeCell n ((n + 2 : ℝ) * (μ - b)) b δ r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
            (extremeFiberAngles ((n + 2 : ℝ) * (μ - b)) p)) ≤
          (C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨δ, C, W, hδ, hδ1, hC, hW, hbound⟩ :=
    exists_actual_full_density_fiber_setIntegral α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, W, hδ, hδ1, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r γ hr
  let s := isotropicRadialParameter α ε
  let a := (n + 2 : ℝ) * (μ - b)
  let K := C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  let I := fun y : Fin n → ℝ =>
    ∫ t in fullExtremeFiber (extremeFiberBase a y) 0 (Fin.last (n + 1)) b δ r,
      actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a (t, y))
  let P := fun y : Fin n → ℝ => ∏ k, W * branchWeight ε (y k + b)
  have hI : Integrable I volume :=
    actualExtremeCell_fiberIntegral_integrable n a b δ r s hs η τ ξ γ hη hτ.1 hξ.1
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
  rw [actualExtremeCell_integral_fubini_box n μ b δ r s hs η τ ξ γ hη hτ.1 hξ.1]
  change (∫ y in remainingAngularBox n μ b r, I y) ≤ K * _
  calc
    _ ≤ ∫ y in remainingAngularBox n μ b r, K * P y :=
      setIntegral_mono_on hI.integrableOn hpint measurableSet_Icc (fun y _ => hpointwise y)
    _ = K * ∫ y in remainingAngularBox n μ b r, P y := integral_const_mul K P
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (remaining_branch_weight_product_integral_bound n W ε μ b r hW.le hε hr) hK

end IsingBulk.AnisoF002.Isotropic
