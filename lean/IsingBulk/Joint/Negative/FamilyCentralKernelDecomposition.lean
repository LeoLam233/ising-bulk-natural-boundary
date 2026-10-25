import IsingBulk.Anisotropic.NegativeCycles.WindingSubsetDecomposition
import IsingBulk.Anisotropic.NegativeCycles.PhysicalCentralSectors
import IsingBulk.Joint.Negative.FamilyIntegralPartition
import IsingBulk.Joint.Negative.FamilyWindingSubsetDecomposition

noncomputable section
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 2000000

theorem compact_family_physical_central_decomposition (B rootB : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q, AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈Q, B (0,eta)≠0)
    (hrB : ∀eta∈Q, AnalyticAt ℂ rootB (0,eta)) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃(R₀ : ℂ→ℂ) (ρ c σ K M : ℝ),0<ρ ∧ 0<c ∧ 0<σ ∧ 0<K ∧ 1≤M ∧
      ∀eta∈Q, ∀m : ℕ, ∀s : ℝ,s<σ →
      ∀curve : ℂ→Coupling, ∀amp : ℂ→ℂ,
      AnalyticAt ℂ curve 0 → AnalyticAt ℂ amp 0 → S (curve 0)≠0 →
      A (curve 0)+T (curve 0)=(Real.cos phi:ℂ)*S (curve 0) →
      |Real.cos phi|<1 → 0<(-T (curve 0)/S (curve 0)).im →
      (∀ᶠt in 𝓝 (0:ℂ), S (curve t)≠0 ∧
        (familyMember B eta) t=T (curve t)/S (curve t) ∧
        transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+(familyMember B eta) t*t ∧
        amp t^2=p (curve t) ∧ amp t/S (curve t)=(familyMember rootB eta) t) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ∀P : (k : Fin (2*m+2)) → (2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C,
      ∀_J : (k : Fin (2*m+2)) → (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) →
        UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C (P k hk) R,
      ∀j : ℕ,
      iteratedDeriv j (fun t=>amp t^(2*m+1)*continuedAngularCoefficient (2*m) (curve t)) 0/(j.factorial:ℂ)=
      2*(iteratedDeriv j (centeredKernelIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))+
      (∑k∈noncentralWindingIndices m,if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
        ∫q in centeredInnerSet (2*m) (windingMean (2*m) k) s,
          constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (windingMean (2*m) k:ℂ) (P k hk).T j
            (complexify (2*m) q) else 0)+(
        (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v)+
        (∑k∈noncentralWindingIndices m,if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
          iteratedDeriv j (centeredInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (windingMean (2*m) k) s
            (P k hk).T) 0/(j.factorial:ℂ) else 0)) ∧
      (∀k hk,‖iteratedDeriv j (centeredInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (windingMean (2*m) k) s
          (P k hk).T) 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) (windingMean (2*m) k) s)).toReal*(K*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) := by
  obtain ⟨R₀,ρ,c,σ,K,M,hρ,hc,hσ,hK,hM,hw⟩ :=
    compact_family_winding_subset_decomposition B rootB phi hphi hQ hB hB0 hrB r C R hr hR hRr
  obtain ⟨a,ha,hphysical⟩ := compact_family_physical_integral_partition B hp hpi hphi hQ hB
  refine ⟨R₀,ρ,c,min σ (min (a^2) (Real.pi^2)),K,M,hρ,hc,
    lt_min hσ (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos Real.pi_pos)),hK,hM,?_⟩
  intro eta heta m s hs curve amp hcurve hA hS hedge hb hBi hchart hres P J j
  let rootB := familyMember rootB eta
  have hsa : s≤a^2 := hs.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsπ : s≤Real.pi^2 := hs.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hw' := hw eta heta m s (hs.trans_le (min_le_left _ _)) P J j (noncentralWindingIndices m)
  refine ⟨?_,hw'.2⟩
  rw [hphysical eta heta m j s hsπ hsa curve amp rootB hcurve hA hS hedge hb hBi hchart hres,
    winding_kernel_sum_two_centers,hw'.1]
  ring

end IsingBulk.Joint.Negative
