import IsingBulk.HT.Final.RightOnsiteRadius
import IsingBulk.Tail.RightFormFactorAnalytic
import IsingBulk.First.ContourParameterDomain

/-! Genuine parameter holomorphy on right-trace neighborhoods for the actual
fixed-radius double contour; no complex extension of an angular bump is used. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Filter Set
open scoped Topology BigOperators

theorem right_onsiteFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    AnalyticAt ℂ (onsiteFormFactor N r) s := by
  have hs0 : s ≠ 0 := by
    intro heq
    have hi : 0 < r⁻¹ := inv_pos.mpr hr
    simp only [heq,sourceS,inv_zero,add_zero,Complex.zero_re] at hm
    linarith
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    (coordinateProduct x*coordinateProduct y)⁻¹*pairProduct x*pairProduct y
  have hfac : ∀ t x y, onsiteDensity t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹ := by
    intro t x y
    dsimp only [A,onsiteDensity,commonDensity]
    ring
  have hf := right_mixedOnsiteDensity_continuous N hN hr hr1
    (rx := r) (ry := r) ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ hm
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)) := by
    apply spatialAmplitude_continuous_of_no_poles hr s
      (right_angularDispersion_ne_zero hr hr1 hm) A
    simpa only [angularResolventProduct_eq,← hfac] using hf
  have ha := rationalDoubleContour_analyticAt_on N hr A hA (rightDampingDomain_isOpen r)
    (fun _ ht => ht.1) (fun _ ht => right_angularDispersion_ne_zero hr hr1 ht.2)
    (s := s) (show s ∈ rightDampingDomain r from ⟨hs0,hm⟩)
  convert! ha using 1
  funext t
  simp only [onsiteFormFactor,rationalDoubleContour,hfac]

theorem rightOnsiteFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 2 < (sourceS s).re) : AnalyticAt ℂ (rightOnsiteFormFactor N) s := by
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hs
  exact (right_onsiteFormFactor_analyticAt N hN hr hr1 hm).congr
    (rightOnsiteFormFactor_eventually_fixed_radius N hN hr hr1 hm).symm

end
end IsingBulk.HT.Final
