import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsCauchy
import IsingBulk.Anisotropic.NegativeDominance.ParticleWeightScaling

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology BigOperators

def physicalOuterCutoffPeriod (n : ℕ) (lam : ℝ) (zeta A : ℂ→ℂ)
    (E : Set (Fin n→ℝ)) (χ : (Fin n→ℝ)→ℂ) (u : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*∫q in E,χ q*(A u)^(n+1)*
    complexAngularDensity lam (zeta u)
      (fun i=>(physicalDependentAngles n (fun k=>q k+Real.pi) i:ℂ))
    ∂Measure.pi (fun _=>edgeAngleMeasure)

/-- The continued outer model is exactly the literal physically weighted
angular cutoff, with the complete lattice multiplier and the correct sign. -/
theorem outerNegativePeriod_eq_physical_cutoff (n : ℕ) {lam b : ℝ}
    {B S A zeta : ℂ→ℂ} (E : Set (Fin n→ℝ)) (χ : (Fin n→ℝ)→ℂ) {u : ℂ}
    (hB : B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : S u=spectralS (zeta u))
    (he : edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hu : 0<u.im) (hBi : 0<(B u).im) :
    outerNegativePeriod b B (fun v=>S v/A v) n E χ u=
      physicalOuterCutoffPeriod n lam zeta A E χ u := by
  unfold outerNegativePeriod physicalOuterCutoffPeriod
  rw [mul_assoc,←integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q=>by
    dsimp only
    rw [negativeShiftedFullIntegrand_div_scale,
      complexAngularDensity_eq_negativeShiftedFullIntegrand n hB hS he hu hBi]
    ring)

theorem outerNegativePeriod_eq_physical_cutoff_jets (n j : ℕ) {lam b : ℝ}
    {B S A zeta f : ℂ→ℂ} (E : Set (Fin n→ℝ)) (χ : (Fin n→ℝ)→ℂ)
    {U V : Set ℂ} (hV : IsOpen V) (hmap : MapsTo f V U)
    (hB : ∀u∈U,B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U,S u=spectralS (zeta u))
    (he : ∀u∈U,edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im) {u : ℂ} (hu : u∈V) :
    iteratedDeriv j (fun t=>outerNegativePeriod b B (fun v=>S v/A v) n E χ (f t)) u=
      iteratedDeriv j (fun t=>physicalOuterCutoffPeriod n lam zeta A E χ (f t)) u := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [hV.mem_nhds hu] with t ht
  exact outerNegativePeriod_eq_physical_cutoff n E χ (hB _ (hmap ht)) (hS _ (hmap ht))
    (he _ (hmap ht)) (hup _ (hmap ht)) (hBi _ (hmap ht))

end
end IsingBulk.Anisotropic.NegativeDominance
