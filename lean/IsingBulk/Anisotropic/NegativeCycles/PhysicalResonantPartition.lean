import IsingBulk.Anisotropic.NegativeCycles.PhysicalJetPartition
import IsingBulk.Anisotropic.NegativeCycles.CenteredInnerGeometry

noncomputable section
set_option maxHeartbeats 1000000
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter
open scoped BigOperators Topology

def windingMean (n : ℕ) (k : Fin (n+2)) : ℝ :=
  ((2*(k.val:ℝ)-(n+1:ℕ))*Real.pi)/(n+1:ℕ)

theorem windingMean_equation (n : ℕ) (k : Fin (n+2)) :
    (n+1:ℕ)*windingMean n k=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi := by
  unfold windingMean
  field_simp

theorem odd_windingMean_ne_zero (m : ℕ) (k : Fin (2*m+2)) : windingMean (2*m) k≠0 := by
  unfold windingMean
  apply div_ne_zero _ (by positivity)
  apply mul_ne_zero _ Real.pi_ne_zero
  intro he
  have hh : (2:ℝ)*(k.val:ℝ)=(2*m+1:ℕ) := sub_eq_zero.mp he
  have hh' : 2*k.val=2*m+1 := by exact_mod_cast hh
  omega

def centeredKernel (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (n : ℕ) (d : ℝ) (q : Fin n→ℝ) (t : ℂ) : ℂ :=
  formFactorNumerator B rootB phi hphi (d:ℂ) t (shapeExtend (complexify n q))*
    cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u (shapeExtend (complexify n q))) t

theorem centeredKernel_function (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (n : ℕ) (d : ℝ) (q : Fin n→ℝ) :
    centeredKernel B rootB phi hphi n d q = (fun t =>
      formFactorNumerator B rootB phi hphi (d:ℂ) t (shapeExtend (complexify n q))*
        cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u (shapeExtend (complexify n q))) t) := rfl

def centeredKernelTaylor (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (n j : ℕ) (d : ℝ) (q : Fin n→ℝ) : ℂ :=
  iteratedDeriv j (centeredKernel B rootB phi hphi n d q) 0/(j.factorial:ℂ)

/-- Full literal resonant particle coefficient, with every actual winding sector.
The inner integrals are genuine arcosh kernel jets, not formal residue surrogates. -/
theorem physical_resonant_winding_partition (B : ℂ→ℂ) {phi : ℝ}
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
        ∑k : Fin (2*m+2),∫q in centeredInnerSet (2*m) (windingMean (2*m) k) σ,
          centeredKernelTaylor B rootB phi hphi (2*m) j (windingMean (2*m) k) q := by
  obtain ⟨r,hr,hw⟩ := actual_inner_winding_jet_integral B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m j σ hσpi hσr lam zeta A rootB hzeta hA hS hedge hb hB hchart hres
  rw [physical_boundary_winding_partition (2*m) (by exact ⟨m,by omega⟩) hzeta hA hS hedge hb hB j σ]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  simpa only [physicalInnerSector,physicalAngularCube,physicalShiftedEnergy,physicalDensityTaylor,
    centeredInnerSet,centeredKernelTaylor,centeredKernel_function,shapeExtend_complexify] using
    hw m j k (windingMean (2*m) k) σ (windingMean_equation _ _) hσpi hσr lam zeta A rootB hchart hres

end IsingBulk.Anisotropic.NegativeCycles
