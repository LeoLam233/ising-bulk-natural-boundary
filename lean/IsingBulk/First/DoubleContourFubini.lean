import IsingBulk.First.AngularFubini

/-! Full coupled double-contour Fubini for any genuinely continuous angular
pullback. This is instantiated separately for all three source normalizations. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

theorem doubleCircleIntegral_eq_product (N : ℕ) (r : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hf : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple r p.1) (angleTuple r p.2))) :
    multiCircleIntegral r N (fun y => multiCircleIntegral r N (fun x => f x y)) =
      ∫ p in angleBox N ×ˢ angleBox N,
        angleProductJacobian r p.2*angleProductJacobian r p.1*f (angleTuple r p.1) (angleTuple r p.2) := by
  have hJ := angleProductJacobian_continuous (N := N) r
  have hinnerCont : Continuous (fun θ : Fin N → ℝ =>
      multiCircleIntegral r N (fun x => f x (angleTuple r θ))) := by
    simp_rw [multiCircleIntegral_eq_angle]
    apply continuous_multiAngleIntegral
    have hj : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian r p.2) :=
      hJ.comp continuous_snd
    have hs : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        f (angleTuple r p.2) (angleTuple r p.1)) := by
      have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (p.2,p.1)) :=
        continuous_snd.prodMk continuous_fst
      convert! hf.comp hc using 1
    exact hj.mul hs
  have hinner (θ : Fin N → ℝ) : multiCircleIntegral r N (fun x => f x (angleTuple r θ)) =
      ∫ ξ in angleBox N, angleProductJacobian r ξ*f (angleTuple r ξ) (angleTuple r θ) := by
    rw [multiCircleIntegral_eq_angle]
    apply multiAngleIntegral_eq_box
    have hc : Continuous (fun ξ : Fin N → ℝ => (ξ,θ)) := continuous_id.prodMk continuous_const
    convert! hJ.mul (hf.comp hc) using 1
  let F : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ := fun p =>
    angleProductJacobian r p.2*angleProductJacobian r p.1*f (angleTuple r p.1) (angleTuple r p.2)
  have hfull : Continuous F := by
    convert! ((hJ.comp continuous_snd).mul (hJ.comp continuous_fst)).mul hf using 1
  have hI : IntegrableOn F (angleBox N ×ˢ angleBox N) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hfull.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have houter : Continuous (fun θ : Fin N → ℝ => angleProductJacobian r θ*
      multiCircleIntegral r N (fun x => f x (angleTuple r θ))) := hJ.mul hinnerCont
  rw [multiCircleIntegral_eq_angle, multiAngleIntegral_eq_box N _ houter]
  change _ = ∫ p in angleBox N ×ˢ angleBox N, F p
  rw [Measure.volume_eq_prod, setIntegral_prod_reverse volume volume _ _ _ hI]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [hinner, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro ξ _
  dsimp only [F]
  ring

end
end IsingBulk.First
