import IsingBulk.Anisotropic.NegativeCycles.PhysicalJetPartition
import IsingBulk.Joint.Negative.CanonicalJets

noncomputable section
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped BigOperators Topology

def physicalDensityTaylor (n : ℕ) (curve : ℂ→Coupling) (amp : ℂ→ℂ) (j : ℕ) (v : Fin n→ℝ) : ℂ :=
  iteratedDeriv j (weightedShiftedPhysicalDensity n curve amp v) 0/(j.factorial:ℂ)

theorem physical_boundary_winding_partition (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ} (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) (j : ℕ) (σ : ℝ) :
    iteratedDeriv j (fun t=>amp t^(n+1)*continuedAngularCoefficient n (curve t)) 0/(j.factorial:ℂ)=
      (∫v in physicalOuterRegion n σ,physicalDensityTaylor n curve amp j v)+
        ∑k : Fin (n+2),∫v in physicalInnerSector n k σ,physicalDensityTaylor n curve amp j v := by
  obtain ⟨hi,he⟩ := weightedShiftedPhysicalDensity_boundary_integral n hn hcurve hA hS hedge hb hB j
  exact he.trans (physical_cube_winding_partition n σ hi)

end IsingBulk.Joint.Negative
