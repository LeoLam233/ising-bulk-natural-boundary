import IsingBulk.Anisotropic.NegativeCycles.WindingSubsetDecomposition
import IsingBulk.Anisotropic.NegativeCycles.PhysicalCentralSectors
import IsingBulk.Anisotropic.NegativeCycles.ActualCentralTransport

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter
open scoped BigOperators Topology
set_option maxHeartbeats 2000000

def centralKernelCapError (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m j : ℕ) (s : ℝ) (T : Config (2*m+1)→ℂ) (Phi : Config (2*m+1)→Config (2*m+1))
    (b : ContDiffBump (0:ℝ)) : ℂ :=
  2*(iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))-
    2*transformedResidueCap B rootB phi hphi m j (Real.pi/(2*m+1:ℕ)) T Phi b

theorem physical_central_higher_decomposition (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃(R₀ : ℂ→ℂ) (ρ c σ K M : ℝ),0<ρ ∧ 0<c ∧ 0<σ ∧ 0<K ∧ 1≤M ∧
      ∀m : ℕ, ∀s : ℝ,s<σ →
      ∀lam : ℝ, ∀zeta A : ℂ→ℂ,
      AnalyticAt ℂ zeta 0 → AnalyticAt ℂ A 0 → spectralS (zeta 0)≠0 →
      spectralA lam (zeta 0)+spectralT lam (zeta 0)=(Real.cos phi:ℂ)*spectralS (zeta 0) →
      |Real.cos phi|<1 → 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im →
      (∀ᶠt in 𝓝 (0:ℂ), spectralS (zeta t)≠0 ∧
        B t=spectralT lam (zeta t)/spectralS (zeta t) ∧
        edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+B t*t ∧
        A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=rootB t) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ∀P : (k : Fin (2*m+2)) → (2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C,
      ∀_J : (k : Fin (2*m+2)) → (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) →
        UniformCorrectionWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C (P k hk) R,
      ∀P0 : UniformProjectedWitness B phi hphi (2*m+1) ((Real.pi/(2*m+1:ℕ):ℝ):ℂ) r C,
      ∀J0 : UniformCorrectionWitness B phi hphi (2*m+1) ((Real.pi/(2*m+1:ℕ):ℝ):ℂ) r C P0 R,
      ∀bump : ContDiffBump (0:ℝ),∀j : ℕ,
      iteratedDeriv j (fun t=>A t^(2*m+1)*continuedAngularCoefficient (2*m) lam (zeta t)) 0/(j.factorial:ℂ)=
      2*transformedResidueCap B rootB phi hphi m j (Real.pi/(2*m+1:ℕ)) P0.T (fun y=>P0.V (J0.W y)) bump+
      (∑k∈noncentralWindingIndices m,if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
        ∫q in centeredInnerSet (2*m) (windingMean (2*m) k) s,
          constrainedResidueDensity B rootB phi hphi (windingMean (2*m) k:ℂ) (P k hk).T j
            (complexify (2*m) q) else 0)+(
        (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) lam zeta A j v)+
        centralKernelCapError B rootB phi hphi m j s P0.T (fun y=>P0.V (J0.W y)) bump+
        (∑k∈noncentralWindingIndices m,if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
          iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s
            (P k hk).T) 0/(j.factorial:ℂ) else 0)) ∧
      (∀k hk,‖iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s
          (P k hk).T) 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) (windingMean (2*m) k) s)).toReal*(K*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) := by
  obtain ⟨R₀,ρ,c,σ,K,M,hρ,hc,hσ,hK,hM,hw⟩ :=
    exists_winding_subset_decomposition B rootB phi hphi hB hB0 hrB r C R hr hR hRr
  obtain ⟨a,ha,hphysical⟩ := physical_resonant_integral_partition B hp hpi hphi hB
  refine ⟨R₀,ρ,c,min σ (min (a^2) (Real.pi^2)),K,M,hρ,hc,
    lt_min hσ (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos Real.pi_pos)),hK,hM,?_⟩
  intro m s hs lam zeta A hzeta hA hS hedge hb hBi hchart hres P J P0 J0 bump j
  have hsa : s≤a^2 := hs.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsπ : s≤Real.pi^2 := hs.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hw' := hw m s (hs.trans_le (min_le_left _ _)) P J j (noncentralWindingIndices m)
  refine ⟨?_,hw'.2⟩
  rw [hphysical m j s hsπ hsa lam zeta A rootB hzeta hA hS hedge hb hBi hchart hres,
    winding_kernel_sum_two_centers,hw'.1]
  unfold centralKernelCapError
  ring

end IsingBulk.Anisotropic.NegativeCycles
