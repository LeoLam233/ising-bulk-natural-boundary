import IsingBulk.Anisotropic.NegativeCycles.PhysicalResonantPartition
import IsingBulk.Anisotropic.NegativeCycles.CenteredKernelTaylor

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter Metric
open scoped BigOperators Topology
set_option maxHeartbeats 1000000

theorem physical_resonant_integral_partition (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0) (hBa : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀m j : ℕ, ∀σ : ℝ,σ≤Real.pi^2 → σ≤r^2 →
      ∀lam : ℝ, ∀zeta A rootB : ℂ→ℂ,
      AnalyticAt ℂ zeta 0 → AnalyticAt ℂ A 0 → spectralS (zeta 0)≠0 →
      spectralA lam (zeta 0)+spectralT lam (zeta 0)=(Real.cos phi:ℂ)*spectralS (zeta 0) →
      |Real.cos phi|<1 → 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im →
      (∀ᶠt in 𝓝 (0:ℂ), spectralS (zeta t)≠0 ∧
        B t=spectralT lam (zeta t)/spectralS (zeta t) ∧
        edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+B t*t ∧
        A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=rootB t) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      iteratedDeriv j (fun t=>A t^(2*m+1)*continuedAngularCoefficient (2*m) lam (zeta t)) 0/(j.factorial:ℂ)=
        (∫v in physicalOuterRegion (2*m) σ,physicalDensityTaylor (2*m) lam zeta A j v)+
        ∑k : Fin (2*m+2),
          iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) σ) 0/(j.factorial:ℂ) := by
  obtain ⟨r,hr,hw⟩ := actual_inner_winding_density_integral B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m j σ hσpi hσr lam zeta A rootB hzeta hA hS hedge hb hB hchart hres
  rw [physical_boundary_winding_partition (2*m) (by exact ⟨m,by omega⟩) hzeta hA hS hedge hb hB j σ]
  obtain ⟨rj,hrj,hj⟩ := weightedShiftedPhysicalDensity_restricted_jets (2*m)
    (by exact ⟨m,by omega⟩) hzeta hA hS hedge hb hB
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  have he := (hj (physicalInnerSector (2*m) k σ) (fun _ hx=>hx.1)).2 j 0 (by simpa using hrj)
  change (∫v in physicalInnerSector (2*m) k σ,
    iteratedDeriv j (weightedShiftedPhysicalDensity (2*m) lam zeta A v) 0/(j.factorial:ℂ))=_
  rw [←he.2]
  have hgerm : (fun t=>∫v in physicalInnerSector (2*m) k σ,
      weightedShiftedPhysicalDensity (2*m) lam zeta A v t) =ᶠ[𝓝 0]
      centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) σ := by
    filter_upwards [hchart,ball_mem_nhds (0:ℂ) hr] with t ht htr
    simpa only [physicalInnerSector,physicalAngularCube,physicalShiftedEnergy,
      weightedShiftedPhysicalDensity,centeredKernelIntegral,centeredInnerSet,shapeExtend_complexify] using
      hw m k (windingMean (2*m) k) σ (windingMean_equation _ _) hσpi hσr t lam (zeta t) (A t)
        rootB (mem_ball_zero_iff.mp htr) ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 hres
  rw [hgerm.iteratedDeriv_eq j]

end IsingBulk.Anisotropic.NegativeCycles
