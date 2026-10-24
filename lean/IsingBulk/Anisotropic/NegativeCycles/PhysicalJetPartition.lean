import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsCanonical
import IsingBulk.Anisotropic.NegativeCycles.PhysicalWindingJets

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped BigOperators Topology

def physicalAngularCube (n : ℕ) : Set (Fin n→ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
def physicalShiftedEnergy (n : ℕ) (v : Fin n→ℝ) : ℝ := ∑i,(negativeShiftedAngles n v i)^2
def physicalOuterRegion (n : ℕ) (σ : ℝ) : Set (Fin n→ℝ) :=
  {v | v∈physicalAngularCube n ∧ σ≤physicalShiftedEnergy n v}
def physicalInnerSector (n : ℕ) (k : Fin (n+2)) (σ : ℝ) : Set (Fin n→ℝ) :=
  {v | v∈physicalAngularCube n ∧ v∈windingSector n k ∧ physicalShiftedEnergy n v<σ}
def physicalDensityTaylor (n : ℕ) (lam : ℝ) (zeta A : ℂ→ℂ) (j : ℕ) (v : Fin n→ℝ) : ℂ :=
  iteratedDeriv j (weightedShiftedPhysicalDensity n lam zeta A v) 0/(j.factorial:ℂ)

theorem physicalShiftedEnergy_measurable (n : ℕ) : Measurable (physicalShiftedEnergy n) :=
  Finset.measurable_sum _ (fun i _ => (negativeShiftedAngles_measurable n i).pow_const 2)

theorem physical_cube_winding_partition (n : ℕ) (σ : ℝ) {g : (Fin n→ℝ)→ℂ}
    (hg : IntegrableOn g (physicalAngularCube n)) :
    (∫v in physicalAngularCube n,g v)=
      (∫v in physicalOuterRegion n σ,g v)+
        ∑k : Fin (n+2),∫v in physicalInnerSector n k σ,g v := by
  let E : Set (Fin n→ℝ) := {v | physicalShiftedEnergy n v<σ}
  have hE : MeasurableSet E := measurableSet_lt (physicalShiftedEnergy_measurable n) measurable_const
  have hsplit := integral_add_compl (μ := volume.restrict (physicalAngularCube n)) hE hg
  rw [Measure.restrict_restrict hE,Measure.restrict_restrict hE.compl] at hsplit
  have houter : Eᶜ∩physicalAngularCube n=physicalOuterRegion n σ := by
    ext v; simp [E,physicalOuterRegion,and_comm]
  have hinner : E∩physicalAngularCube n=physicalAngularCube n∩E := inter_comm _ _
  rw [houter,hinner] at hsplit
  have hi : IntegrableOn g (physicalAngularCube n∩E) := hg.mono_set inter_subset_left
  have hU : MeasurableSet (physicalAngularCube n∩E) := measurableSet_Icc.inter hE
  rw [integral_winding_partition n hU hi] at hsplit
  have hsets (k : Fin (n+2)) : (physicalAngularCube n∩E)∩windingSector n k=physicalInnerSector n k σ := by
    ext v; simp only [mem_inter_iff,physicalInnerSector,mem_ofPred_eq,E]; tauto
  simp_rw [hsets] at hsplit
  exact hsplit.symm.trans (add_comm _ _)

theorem physical_boundary_winding_partition (n : ℕ) (hn : Odd (n+1))
    {lam b : ℝ} {zeta A : ℂ→ℂ} (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im) (j : ℕ) (σ : ℝ) :
    iteratedDeriv j (fun t=>A t^(n+1)*continuedAngularCoefficient n lam (zeta t)) 0/(j.factorial:ℂ)=
      (∫v in physicalOuterRegion n σ,physicalDensityTaylor n lam zeta A j v)+
        ∑k : Fin (n+2),∫v in physicalInnerSector n k σ,physicalDensityTaylor n lam zeta A j v := by
  obtain ⟨hi,he⟩ := weightedShiftedPhysicalDensity_boundary_integral n hn hzeta hA hS hedge hb hB j
  exact he.trans (physical_cube_winding_partition n σ hi)

end IsingBulk.Anisotropic.NegativeCycles
