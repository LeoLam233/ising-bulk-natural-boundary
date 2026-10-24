import IsingBulk.Anisotropic.NegativeCycles.LocalDensityAnalytic
import IsingBulk.Anisotropic.NegativeCycles.LocalPhysicalDensity

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem exists_local_formFactor_subtraction (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀d : ℂ, ∀v : Config (2*m+1), ∀T : Config (2*m+1)→ℂ,
      ‖T v‖<r → (∀i, ‖d+v i‖<r) → poleEquation B phi hphi d (T v) v=0 →
      poleParameterDerivative B phi hphi d (T v) v≠0 →
      ∃R : ℂ→ℂ, AnalyticAt ℂ R (T v) ∧ ∀t : ℂ, t≠T v →
        formFactorNumerator B rootB phi hphi d t v * cothHalf (fun u => poleEquation B phi hphi d u v) t=
          -poleResidue B rootB phi hphi d T v/(t-T v)+R t := by
  obtain ⟨r,hr0,ha⟩ := local_density_phase_analytic B rootB phi hphi hB hr
  refine ⟨r,hr0,?_⟩
  intro m d v T hT hv hzero hd
  obtain ⟨hN,hF⟩ := ha m d (T v) v hT hv
  obtain ⟨R,hR,he⟩ := exists_analytic_coth_subtraction hF hN hzero hd
  refine ⟨R,hR,?_⟩
  intro t ht
  rw [he t ht]
  unfold poleResidue poleParameterDerivative
  ring

/-- Exact simple-pole subtraction of the literal normalized physical density.
The remainder is genuinely analytic at the actual pole, not a stipulated error. -/
theorem exists_local_physical_pole_subtraction (B rootB : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀d : ℂ, ∀v : Config (2*m+1), ∀T : Config (2*m+1)→ℂ,
      ‖T v‖<r → (∀i, ‖d+v i‖<r) → poleEquation B phi hphi d (T v) v=0 →
      poleParameterDerivative B phi hphi d (T v) v≠0 →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ∃R : ℂ→ℂ, AnalyticAt ℂ R (T v) ∧
        ∀t z A : ℂ, ∀lam : ℝ, ‖t‖<r → t≠T v → spectralS z≠0 →
          B t=spectralT lam z/spectralS z →
          edgeMapV lam (-1) z=(Real.cos phi:ℂ)+B t*t →
          A^2=spectralProduct lam z → A/spectralS z=rootB t →
          A^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
            continuedAngularDensity lam z (fun i => (Real.pi:ℂ)+d+v i)=
              -poleResidue B rootB phi hphi d T v/(t-T v)+R t := by
  obtain ⟨r0,hr0,hsub⟩ := exists_local_formFactor_subtraction B rootB phi hphi hB hr
  obtain ⟨r1,hr1,hphys⟩ := local_scaled_physical_density B hp hpi hphi hB
  refine ⟨min r0 r1,lt_min hr0 hr1,?_⟩
  intro m d v T hT hv hzero hd hres
  obtain ⟨R,hR,he⟩ := hsub m d v T (hT.trans_le (min_le_left _ _))
    (fun i => (hv i).trans_le (min_le_left _ _)) hzero hd
  refine ⟨R,hR,?_⟩
  intro t z A lam ht htT hS hBt hchart hA hAR
  rw [hphys m d t v lam z A rootB (ht.trans_le (min_le_right _ _))
    (fun i => (hv i).trans_le (min_le_right _ _)) hS hBt hchart hA hAR hres]
  exact he t htT

end IsingBulk.Anisotropic.NegativeCycles
