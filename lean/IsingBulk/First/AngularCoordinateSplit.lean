import IsingBulk.First.AngularFubini

/-! Genuine finite Fubini with any chosen angular coordinate innermost. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

theorem angleBox_integral_succAbove (n : ℕ) (i : Fin (n+1))
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Continuous f) :
    (∫ θ in angleBox (n+1), f θ) = ∫ θ in angleBox n,
      ∫ u : ℝ in 0..2*Real.pi, f (i.insertNth u θ) := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ), e p = i.insertNth p.1 p.2 := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hbox : e ⁻¹' angleBox (n+1) = Icc (0:ℝ) (2*Real.pi) ×ˢ angleBox n := by
    exact ((Fin.insertNthOrderIso (fun _ => ℝ) i).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  have hcomp : Continuous (fun p : ℝ × (Fin n → ℝ) => f (e p)) := by
    simp only [he]
    apply hf.comp
    fun_prop
  have hi : IntegrableOn (fun p => f (e p)) (Icc (0:ℝ) (2*Real.pi) ×ˢ angleBox n)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hcomp.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← hem.map_eq, setIntegral_map_equiv, hbox, Measure.volume_eq_prod,
    setIntegral_prod_reverse volume volume _ _ _ hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  dsimp only
  rw [he]

end
end IsingBulk.First
