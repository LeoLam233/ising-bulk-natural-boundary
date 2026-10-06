import IsingBulk.Tail.RightRadiusIndependence
import IsingBulk.First.ContourParameterDomain

/-! Genuine parameter holomorphy on right-trace neighborhoods for the actual
fixed-radius double contour; no complex extension of an angular bump is used. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter Set
open scoped Topology BigOperators

def rightDampingDomain (r : ℝ) : Set ℂ := {s | s ≠ 0 ∧ 1+r⁻¹ < (sourceS s).re}

theorem rightDampingDomain_isOpen (r : ℝ) : IsOpen (rightDampingDomain r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hc : ContinuousAt (fun t : ℂ => (sourceS t).re) s :=
    Complex.continuous_re.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs.1)) rfl
  filter_upwards [eventually_ne_nhds hs.1,hc.eventually (Ioi_mem_nhds hs.2)] with t ht0 ht
  exact ⟨ht0,ht⟩

theorem right_angularDispersion_ne_zero {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) :
    sourceS s-angularDispersionTrace r i p ≠ 0 := by
  rw [sourceS_sub_angularDispersionTrace]
  have hx : ‖anglePoint r (p.1 i)‖ = r := anglePoint_norm hr.le _
  have hy : ‖anglePoint r (p.2 i)‖ = r := anglePoint_norm hr.le _
  have hpos := right_dispersion_re_positive_on_annulus hr (by rw [hx]) (by rw [hy])
    (by rw [hx]; exact hr1.le) (by rw [hy]; exact hr1.le) hm
  exact fun hzero => (ne_of_gt hpos) (congrArg Complex.re hzero)

theorem right_doubleFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    AnalyticAt ℂ (doubleFormFactor N r) s := by
  have hs0 : s ≠ 0 := by
    intro heq
    have hi : 0 < r⁻¹ := inv_pos.mpr hr
    simp only [heq,sourceS,inv_zero,add_zero,Complex.zero_re] at hm
    linarith
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y
  have hfac : ∀ t x y, doubleDensity t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹ := by
    intro t x y
    dsimp only [A,doubleDensity,commonDensity]
    ring
  have hf := right_mixedDoubleDensity_continuous N hN hr hr1
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
  simp only [doubleFormFactor,rationalDoubleContour,hfac]

theorem rightFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 2 < (sourceS s).re) : AnalyticAt ℂ (rightFormFactor N) s := by
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hs
  exact (right_doubleFormFactor_analyticAt N hN hr hr1 hm).congr
    (rightFormFactor_eventually_fixed_radius N hN hr hr1 hm).symm

end
end IsingBulk.Tail
