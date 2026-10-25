import IsingBulk.Anisotropic.NegativeCycles.PhysicalResonantPartition
import IsingBulk.Joint.Negative.JetPartition

noncomputable section
set_option maxHeartbeats 1000000
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter
open scoped BigOperators Topology

/-- Full literal resonant particle coefficient, with every actual winding sector.
The inner integrals are genuine arcosh kernel jets, not formal residue surrogates. -/
theorem physical_resonant_winding_partition (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0) (hBa : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀m j : ℕ, ∀σ : ℝ,σ≤Real.pi^2 → σ≤r^2 →
      ∀curve : ℂ→Coupling, ∀amp rootB : ℂ→ℂ,
      AnalyticAt ℂ curve 0 → AnalyticAt ℂ amp 0 → S (curve 0)≠0 →
      A (curve 0)+T (curve 0)=(Real.cos phi:ℂ)*S (curve 0) →
      |Real.cos phi|<1 → 0<(-T (curve 0)/S (curve 0)).im →
      (∀ᶠt in 𝓝 (0:ℂ), S (curve t)≠0 ∧
        B t=T (curve t)/S (curve t) ∧
        transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+B t*t ∧
        amp t^2=p (curve t) ∧ amp t/S (curve t)=rootB t) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      iteratedDeriv j (fun t=>amp t^(2*m+1)*continuedAngularCoefficient (2*m) (curve t)) 0/(j.factorial:ℂ)=
        (∫v in physicalOuterRegion (2*m) σ,physicalDensityTaylor (2*m) curve amp j v)+
        ∑k : Fin (2*m+2),∫q in centeredInnerSet (2*m) (windingMean (2*m) k) σ,
          centeredKernelTaylor B rootB phi hphi (2*m) j (windingMean (2*m) k) q := by
  obtain ⟨r,hr,hw⟩ := actual_inner_winding_jet_integral B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m j σ hσpi hσr curve amp rootB hcurve hA hS hedge hb hB hchart hres
  rw [physical_boundary_winding_partition (2*m) (by exact ⟨m,by omega⟩) hcurve hA hS hedge hb hB j σ]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  simpa only [physicalInnerSector,physicalAngularCube,physicalShiftedEnergy,physicalDensityTaylor,
    centeredInnerSet,centeredKernelTaylor,centeredKernel_function,shapeExtend_complexify] using
    hw m j k (windingMean (2*m) k) σ (windingMean_equation _ _) hσpi hσr curve amp rootB hchart hres

end IsingBulk.Joint.Negative
