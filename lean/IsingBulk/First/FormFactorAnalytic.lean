import IsingBulk.First.FixedRadiusAnalytic
import IsingBulk.First.GlobalResidueRoot
import IsingBulk.First.RadiusIndependence

/-! Holomorphy of the actual offsite, onsite and full-site fixed-radius
form factors, derived by compact-domain differentiation of their densities. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem dampingDomain_of_margin {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) : s ∈ dampingDomain r := by
  refine ⟨?_, hm⟩
  intro he
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  simp only [he, sourceS, inv_zero, add_zero, Complex.zero_im] at hm
  linarith

theorem sourceFormFactor_analyticAt (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hs : s ∈ dampingDomain r)
    (f : ℂ → (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hfac : ∀ t x y, f t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹)
    (hf : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => f s (angleTuple r p.1) (angleTuple r p.2))) :
    AnalyticAt ℂ (fun t => (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
      multiCircleIntegral r N (fun x => f t x y))) s := by
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => A (angleTuple r p.1) (angleTuple r p.2)) := by
    apply spatialAmplitude_continuous hr hr1 hs A
    simpa only [angularResolventProduct_eq, ← hfac] using hf
  have ha := rationalDoubleContour_analyticAt N hr hr1 A hA hs
  convert! ha using 1
  funext t
  simp only [rationalDoubleContour, hfac]

/-- These are the literal normalized integrals, not a replacement observable.
The radius stays fixed on the full complex neighborhood. -/
theorem formFactors_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    AnalyticAt ℂ (doubleFormFactor N r) s ∧ AnalyticAt ℂ (onsiteFormFactor N r) s ∧
      AnalyticAt ℂ (standardFormFactor N r) s := by
  have hs := dampingDomain_of_margin hr hr1 hm
  have hroot := globalRoot_admissible hr hr1 hm
  have htuple : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => globalRoot s (anglePoint r (θ i))) := by
    intro θ
    exact hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _)
  have hD := doubleDensity_continuous_angles N hN r s (globalRoot s) htuple
  obtain ⟨hO,hS⟩ := normalizationDensities_continuous_angles N hN r s (globalRoot s) hroot
  constructor
  · apply sourceFormFactor_analyticAt N hr hr1 hs doubleDensity
      (fun x y => ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
        ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y) _ hD
    intro t x y
    unfold doubleDensity commonDensity
    ring
  constructor
  · apply sourceFormFactor_analyticAt N hr hr1 hs onsiteDensity
      (fun x y => (coordinateProduct x*coordinateProduct y)⁻¹*pairProduct x*pairProduct y) _ hO
    intro t x y
    unfold onsiteDensity commonDensity
    ring
  · apply sourceFormFactor_analyticAt N hr hr1 hs standardDensity
      (fun x y => (1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)/
        ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y) _ hS
    intro t x y
    unfold standardDensity commonDensity
    ring

theorem upperFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 0 < (sourceS s).im) : AnalyticAt ℂ (upperFormFactor N) s := by
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hs
  exact ((formFactors_analyticAt N hN hr hr1 hm).1).congr
    (upperFormFactor_eventually_fixed_radius N hN hr hr1 hm).symm

end
end IsingBulk.First
