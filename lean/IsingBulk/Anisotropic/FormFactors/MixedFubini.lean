import IsingBulk.First.MixedDoubleContour

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set MeasureTheory

theorem mixedDoubleContour_eq_box (N : ℕ) (rx ry : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hD : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple rx p.1) (angleTuple ry p.2))) :
    multiCircleIntegral ry N (fun y => multiCircleIntegral rx N (fun x => f x y)) =
    ∫ p in angleBox N ×ˢ angleBox N,
      angleProductJacobian ry p.2 * angleProductJacobian rx p.1 *
        f (angleTuple rx p.1) (angleTuple ry p.2) := by
  have hJx := angleProductJacobian_continuous (N := N) rx
  have hJy := angleProductJacobian_continuous (N := N) ry
  have hinnerCont : Continuous (fun θ : Fin N → ℝ =>
      multiCircleIntegral rx N (fun x => f x (angleTuple ry θ))) := by
    simp_rw [multiCircleIntegral_eq_angle]
    apply continuous_multiAngleIntegral
    have hj : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian rx p.2) :=
      hJx.comp continuous_snd
    have hs : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        f (angleTuple rx p.2) (angleTuple ry p.1)) := by
      have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (p.2,p.1)) :=
        continuous_snd.prodMk continuous_fst
      convert! hD.comp hc using 1
    exact hj.mul hs
  have hinner (θ : Fin N → ℝ) : multiCircleIntegral rx N (fun x => f x (angleTuple ry θ)) =
      ∫ ξ in angleBox N, angleProductJacobian rx ξ * f (angleTuple rx ξ) (angleTuple ry θ) := by
    rw [multiCircleIntegral_eq_angle]
    apply multiAngleIntegral_eq_box
    have hc : Continuous (fun ξ : Fin N → ℝ => (ξ,θ)) := continuous_id.prodMk continuous_const
    convert! hJx.mul (hD.comp hc) using 1
  have hfull : Continuous ((fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian ry p.2 * angleProductJacobian rx p.1 * f (angleTuple rx p.1) (angleTuple ry p.2))) := by
    convert! ((hJy.comp continuous_snd).mul (hJx.comp continuous_fst)).mul hD using 1
  have hI : IntegrableOn ((fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian ry p.2 * angleProductJacobian rx p.1 * f (angleTuple rx p.1) (angleTuple ry p.2)))
      (angleBox N ×ˢ angleBox N) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hfull.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have houter : Continuous (fun θ : Fin N → ℝ => angleProductJacobian ry θ *
      multiCircleIntegral rx N (fun x => f x (angleTuple ry θ))) := hJy.mul hinnerCont
  rw [multiCircleIntegral_eq_angle, multiAngleIntegral_eq_box N _ houter,
    Measure.volume_eq_prod, setIntegral_prod_reverse volume volume _ _ _ hI]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [hinner, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro ξ _
  dsimp only
  ring


theorem mixedDoubleContour_swap (N : ℕ) (rx ry : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hD : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple rx p.1) (angleTuple ry p.2))) :
    multiCircleIntegral ry N (fun y => multiCircleIntegral rx N (fun x => f x y)) =
      multiCircleIntegral rx N (fun x => multiCircleIntegral ry N (fun y => f x y)) := by
  have hs : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple rx p.2) (angleTuple ry p.1)) := by
    exact hD.comp (continuous_snd.prodMk continuous_fst)
  rw [mixedDoubleContour_eq_box N rx ry f hD,
    mixedDoubleContour_eq_box N ry rx (fun y x => f x y) hs]
  rw [Measure.volume_eq_prod,
    ← setIntegral_prod_swap (angleBox N) (angleBox N)]
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  dsimp only [Prod.swap]
  ring
end
end IsingBulk.Anisotropic.FormFactors
