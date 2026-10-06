import IsingBulk.First.PeriodicLiftIntegral

/-! Exact product-torus shifts for the actual two angular coordinate families. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

def DoubleCoordinatePeriodicSections (N : ℕ)
    (F : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ) : Prop :=
  (∀ y, CoordinatePeriodic N (fun x => F (x,y))) ∧
  (∀ x, CoordinatePeriodic N (fun y => F (x,y)))

theorem doubleAngleBox_eq_iterated (N : ℕ)
    (F : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ) (hF : Continuous F) :
    (∫ p in angleBox N ×ˢ angleBox N, F p) =
      ∫ y in angleBox N, ∫ x in angleBox N, F (x,y) := by
  rw [Measure.volume_eq_prod]
  apply setIntegral_prod_reverse volume volume
  rw [← Measure.volume_eq_prod]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem doubleAngleBox_integral_shift (N : ℕ)
    (F : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ) (hF : Continuous F)
    (hp : DoubleCoordinatePeriodicSections N F) (c : (Fin N → ℝ) × (Fin N → ℝ)) :
    (∫ p in angleBox N ×ˢ angleBox N, F (p+c)) = ∫ p in angleBox N ×ˢ angleBox N, F p := by
  have hFc : Continuous (fun p => F (p+c)) := hF.comp (continuous_id.add continuous_const)
  let g : (Fin N → ℝ) → ℂ := fun y => ∫ x in angleBox N, F (x,y)
  have hgc : Continuous g := by
    apply continuous_parametric_integral_of_continuous (s := angleBox N) _ isCompact_Icc
    exact hF.comp (continuous_snd.prodMk continuous_fst)
  have hgp : CoordinatePeriodic N g := by
    intro y i
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact hp.2 x y i
  rw [doubleAngleBox_eq_iterated N _ hFc, doubleAngleBox_eq_iterated N F hF]
  calc
    _ = ∫ y in angleBox N, g (y+c.2) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _
      exact angleBox_integral_shift N (fun x => F (x,y+c.2))
        (hF.comp (continuous_id.prodMk continuous_const)) (hp.1 (y+c.2)) c.1
    _ = _ := angleBox_integral_shift N g hgc hgp c.2

end
end IsingBulk.First
