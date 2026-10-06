import IsingBulk.First.FarExteriorAnnularDensity
import IsingBulk.First.MixedDoubleContour

/-! Actual mixed source-contour continuity and Fubini in the far-exterior norm
domain. The integrability is derived from genuine compact angular continuity. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

set_option maxHeartbeats 800000 in
theorem farExterior_mixedDoubleDensity_continuous (N : ℕ) (hN : 0 < N) {r R rx ry : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hR : R < 1) (hx : r ≤ rx ∧ rx ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hs : 16 < ‖s‖) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      doubleDensity s (angleTuple rx p.1) (angleTuple ry p.2)) := by
  have hsap : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      (angleTuple rx p.1, angleTuple ry p.2)) :=
    ((angleTuple_continuous (N := N) rx).comp continuous_fst).prodMk
      ((angleTuple_continuous (N := N) ry).comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hpx : angleTuple rx p.1 ∈ annularProduct N r R := by
    intro i
    change r ≤ ‖anglePoint rx (p.1 i)‖ ∧ ‖anglePoint rx (p.1 i)‖ ≤ R
    rw [anglePoint_norm ((show 0 < r by linarith).trans_le hx.1).le]
    exact hx
  have hpy : angleTuple ry p.2 ∈ annularProduct N r R := by
    intro i
    change r ≤ ‖anglePoint ry (p.2 i)‖ ∧ ‖anglePoint ry (p.2 i)‖ ≤ R
    rw [anglePoint_norm ((show 0 < r by linarith).trans_le hy.1).le]
    exact hy
  have hd := farExterior_doubleDensity_differentiableAt_maps hN hr hR hs
    (Prod.fst : (Fin N → ℂ) × (Fin N → ℂ) → (Fin N → ℂ)) Prod.snd
    (angleTuple rx p.1, angleTuple ry p.2) differentiableAt_fst differentiableAt_snd hpx hpy
  have hc : ContinuousAt (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      (angleTuple rx q.1, angleTuple ry q.2)) p := hsap.continuousAt
  convert! hd.continuousAt.comp_of_eq hc rfl using 1

theorem farExterior_mixedDoubleFormFactor_eq_product (N : ℕ) (hN : 0 < N) {r R rx ry : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hR : R < 1) (hx : r ≤ rx ∧ rx ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hs : 16 < ‖s‖) :
    mixedDoubleFormFactor N rx ry s = (N.factorial:ℂ)⁻¹ *
      ∫ p in angleBox N ×ˢ angleBox N, mixedDoubleAngleDensity rx ry s p := by
  have hD := farExterior_mixedDoubleDensity_continuous N hN hr hR hx hy hs
  have hJx := angleProductJacobian_continuous (N := N) rx
  have hJy := angleProductJacobian_continuous (N := N) ry
  have hinnerCont : Continuous (fun θ : Fin N → ℝ =>
      multiCircleIntegral rx N (fun x => doubleDensity s x (angleTuple ry θ))) := by
    simp_rw [multiCircleIntegral_eq_angle]
    apply continuous_multiAngleIntegral
    have hj : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian rx p.2) :=
      hJx.comp continuous_snd
    have hs : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        doubleDensity s (angleTuple rx p.2) (angleTuple ry p.1)) := by
      have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (p.2,p.1)) :=
        continuous_snd.prodMk continuous_fst
      convert! hD.comp hc using 1
    exact hj.mul hs
  have hinner (θ : Fin N → ℝ) : multiCircleIntegral rx N (fun x => doubleDensity s x (angleTuple ry θ)) =
      ∫ ξ in angleBox N, angleProductJacobian rx ξ * doubleDensity s (angleTuple rx ξ) (angleTuple ry θ) := by
    rw [multiCircleIntegral_eq_angle]
    apply multiAngleIntegral_eq_box
    have hc : Continuous (fun ξ : Fin N → ℝ => (ξ,θ)) := continuous_id.prodMk continuous_const
    convert! hJx.mul (hD.comp hc) using 1
  have hfull : Continuous (mixedDoubleAngleDensity (N := N) rx ry s) := by
    convert! ((hJy.comp continuous_snd).mul (hJx.comp continuous_fst)).mul hD using 1
  have hI : IntegrableOn (mixedDoubleAngleDensity (N := N) rx ry s)
      (angleBox N ×ˢ angleBox N) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hfull.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have houter : Continuous (fun θ : Fin N → ℝ => angleProductJacobian ry θ *
      multiCircleIntegral rx N (fun x => doubleDensity s x (angleTuple ry θ))) := hJy.mul hinnerCont
  unfold mixedDoubleFormFactor
  congr 1
  rw [multiCircleIntegral_eq_angle, multiAngleIntegral_eq_box N _ houter,
    Measure.volume_eq_prod, setIntegral_prod_reverse volume volume _ _ _ hI]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [hinner, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro ξ _
  dsimp only [mixedDoubleAngleDensity]
  ring

/-- Scalar contour measures commute by genuine absolute-integrable Fubini. -/
theorem farExterior_mixedDoubleFormFactor_swap (N : ℕ) (hN : 0 < N) {r R rx ry : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hR : R < 1) (hx : r ≤ rx ∧ rx ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hs : 16 < ‖s‖) :
    mixedDoubleFormFactor N rx ry s = mixedDoubleFormFactor N ry rx s := by
  rw [farExterior_mixedDoubleFormFactor_eq_product N hN hr hR hx hy hs,
    farExterior_mixedDoubleFormFactor_eq_product N hN hr hR hy hx hs]
  congr 1
  rw [Measure.volume_eq_prod,
    ← setIntegral_prod_swap (angleBox N) (angleBox N) (mixedDoubleAngleDensity ry rx s)]
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  dsimp only [mixedDoubleAngleDensity, Prod.swap]
  rw [doubleDensity_swap s (angleTuple rx p.1) (angleTuple ry p.2)]
  ring

end
end IsingBulk.First
