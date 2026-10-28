import IsingBulk.HT22.Geometry.CompactSlope

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter IsingBulk.Preferred22

def angularInverseSlopeValue (S w : ℂ) : ℂ := (1+preferredPhaseSlope S w)⁻¹

theorem phaseSlope_hasDerivAt_of_analytic (S w : ℂ)
    (ha : AnalyticAt ℂ preferredArccos (S-Complex.cos w))
    (hs : Complex.sin (preferredArccos (S-Complex.cos w)) ≠ 0) :
    HasDerivAt (preferredPhaseSlope S) (-preferredPhaseCurvature S w) w := by
  let φ := fun z : ℂ => preferredArccos (S-Complex.cos z)
  have hφ : AnalyticAt ℂ φ w :=
    AnalyticAt.comp (f := fun z : ℂ => S-Complex.cos z) (g := preferredArccos) ha (by fun_prop)
  have hc := hφ.differentiableAt.hasDerivAt.ccos
  have hdisp : (fun z => Complex.cos (φ z)) =ᶠ[𝓝 w] (fun z => S-Complex.cos z) :=
    Filter.Eventually.of_forall (fun z => cos_preferredArccos _)
  have he := (hc.congr_of_eventuallyEq hdisp.symm).unique ((Complex.hasDerivAt_cos w).const_sub S)
  have hp : deriv φ w = preferredPhaseSlope S w := by
    unfold preferredPhaseSlope
    apply (eq_div_iff hs).2
    simp only [neg_neg] at he
    linear_combination -he
  have hd := ((Complex.hasDerivAt_sin w).neg).div
    ((Complex.hasDerivAt_sin (φ w)).comp w hφ.differentiableAt.hasDerivAt) hs
  rw [hp] at hd
  convert! hd using 1
  unfold preferredPhaseSlope preferredPhaseCurvature
  simp only [Function.comp_apply, Pi.neg_apply]
  have htrig := Complex.sin_sq_add_cos_sq (φ w)
  have hcos : Complex.cos (φ w)=S-Complex.cos w := cos_preferredArccos _
  rw [hcos] at htrig
  change _ = _
  rw [hcos]
  have hsn : Complex.sin (φ w) ≠ 0 := hs
  field_simp [hs,hsn]
  linear_combination (Complex.sin (φ w))^2*Complex.cos w*htrig+
    (Complex.sin (φ w))^2*(S-Complex.cos w)*(Complex.sin_sq_add_cos_sq w)

theorem angularInverseSlopeValue_hasDerivAt (S w : ℂ)
    (ha : AnalyticAt ℂ preferredArccos (S-Complex.cos w))
    (hs : Complex.sin (preferredArccos (S-Complex.cos w)) ≠ 0)
    (hden : 1+preferredPhaseSlope S w ≠ 0) :
    HasDerivAt (angularInverseSlopeValue S) (angularInverseSlopeDerivative S w) w := by
  have h := ((phaseSlope_hasDerivAt_of_analytic S w ha hs).const_add 1).inv hden
  convert! h using 1
  simp only [angularInverseSlopeDerivative, neg_neg]

/-- A local identity of genuine analytic functions transfers the ratio
calculus to canonical literal Uv before composing any real occupancy arc. -/
theorem inverseV_along_angle_hasDerivAt (t w : ℂ)
    (ha : AnalyticAt ℂ preferredArccos (temperatureTrace t-Complex.cos w))
    (hc : Complex.cos ((w+physicalPhase t w)/2) ≠ 0)
    (hl : 0<((physicalPhase t w-w)/2).re)
    (hu : ((physicalPhase t w-w)/2).re<Real.pi)
    (hs : Complex.sin (physicalPhase t w) ≠ 0)
    (hden : 1+preferredPhaseSlope (temperatureTrace t) w ≠ 0) :
    HasDerivAt (fun z => inverseV t (sumCoordinate t z))
      (angularInverseSlopeDerivative (temperatureTrace t) w) w := by
  have hp : AnalyticAt ℂ (physicalPhase t) w :=
    AnalyticAt.comp (f := fun z : ℂ => temperatureTrace t-Complex.cos z)
      (g := preferredArccos) ha (by fun_prop)
  have hhalf := Complex.continuous_re.continuousAt.comp
    ((hp.continuousAt.sub continuousAt_id).div_const 2)
  have hcc := Complex.continuous_cos.continuousAt.comp
    ((continuousAt_id.add hp.continuousAt).div_const 2)
  have hss := Complex.continuous_sin.continuousAt.comp hp.continuousAt
  have heq : (fun z => inverseV t (sumCoordinate t z)) =ᶠ[𝓝 w]
      angularInverseSlopeValue (temperatureTrace t) := by
    filter_upwards [hcc.eventually_ne hc,
      (continuousAt_const : ContinuousAt (fun _ : ℂ => (0:ℝ)) w).eventually_lt hhalf hl,
      hhalf.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℂ => Real.pi) w) hu,
      hss.eventually_ne hs] with z hcz hlz huz hsz
    have he := inverseV_source_ratio t z (physicalPhase t z)
      (by rw [physicalPhase,cos_preferredArccos]; ring) hcz hlz huz hsz
    change Complex.sin (physicalPhase t z) ≠ 0 at hsz
    change inverseV t (z+physicalPhase t z) = _
    rw [he]
    unfold angularInverseSlopeValue preferredPhaseSlope
    change _ = (1+-Complex.sin z/Complex.sin (physicalPhase t z))⁻¹
    rw [show 1+-Complex.sin z/Complex.sin (physicalPhase t z) =
      (Complex.sin (physicalPhase t z)-Complex.sin z)/Complex.sin (physicalPhase t z) by
        field_simp [hsz]; ring]
    rw [inv_div]
  exact (angularInverseSlopeValue_hasDerivAt (temperatureTrace t) w ha hs hden).congr_of_eventuallyEq heq

end
end IsingBulk.HT22.Geometry
