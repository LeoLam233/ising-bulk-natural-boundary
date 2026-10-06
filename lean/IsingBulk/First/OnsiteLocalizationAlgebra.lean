import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.OnsiteAuxiliaryInterchange
import IsingBulk.First.NormalizationIntegral

/-! Fixed, temperature-independent localization weights preserve analyticity of
the actual normalized integrals. Residue equality transfers this regularity to
the selected root representation without differentiating a varying radius. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem localizedOnsiteFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hw : Continuous w) :
    AnalyticAt ℂ (fun t => localizedOnsiteFormFactor N r t w) s := by
  have hs := dampingDomain_of_margin hr hr1 hm
  have hroot := globalRoot_admissible hr hr1 hm
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    (coordinateProduct x*coordinateProduct y)⁻¹*pairProduct x*pairProduct y
  have hfac (t : ℂ) (x y : Fin N → ℂ) :
      onsiteDensity t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹ := by
    dsimp only [A, onsiteDensity, commonDensity]
    ring
  have hD := (normalizationDensities_continuous_angles N hN r s (globalRoot s) hroot).1
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => A (angleTuple r p.1) (angleTuple r p.2)) := by
    apply spatialAmplitude_continuous hr hr1 hs A
    simpa only [angularResolventProduct_eq, ← hfac] using hD
  let aw : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ := fun p =>
    (w p:ℂ)*angleProductJacobian r p.2*angleProductJacobian r p.1*A (angleTuple r p.1) (angleTuple r p.2)
  have hJ := angleProductJacobian_continuous (N := N) r
  have haw : Continuous aw :=
    ((((Complex.continuous_ofReal.comp hw).mul (hJ.comp continuous_snd)).mul
      (hJ.comp continuous_fst))).mul hA
  have ha := (analyticAt_const (𝕜 := ℂ) (x := s) (v := (N.factorial:ℂ)⁻¹)).mul
    (angularResolventIntegral_analyticAt N hr hr1 aw haw hs)
  convert! ha using 1
  funext t
  dsimp only [Pi.mul_apply, localizedOnsiteFormFactor]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  dsimp only [localizedOnsiteAngleDensity, aw]
  rw [hfac, angularResolventProduct_eq]
  ring


end
end IsingBulk.First
