import IsingBulk.Anisotropic.NegativeCycles.PhaseRoot
import IsingBulk.Anisotropic.NegativeCycles.DensityPhaseBridge

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Tail IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges
open Set Filter Metric
open scoped Topology BigOperators

theorem paper_rootB_sq {lam : ℝ} {z A : ℂ} (hS : spectralS z≠0)
    (hA : A^2=spectralProduct lam z) : (A/spectralS z)^2=spectralT lam z/spectralS z := by
  rw [div_pow,hA,spectralProduct]
  field_simp

theorem negativePhase_root_uniform (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀t delta : ℂ, ‖t‖<r → ‖delta‖<r →
      continuedRoot (negativeDispersion B (Real.cos phi) t delta)=
        Complex.exp (-negativePhase B phi hphi t delta) := by
  obtain ⟨r,hr,he⟩ := Metric.eventually_nhds_iff.mp
    (continuedRoot_negativeDispersion_eq_exp_eventually B hp hpi hphi hB)
  refine ⟨r,hr,?_⟩
  intro t delta ht hd
  apply he (y := (t,delta))
  change dist (t,delta) (0 : ℂ × ℂ)<r
  simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro ht hd

/-- Actual normalized physical density in a common complex local chart.
The arcosh/root identity is proved internally, for all particle indices. -/
theorem local_scaled_physical_density (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0)
    (hBa : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀d t : ℂ, ∀v : Config (2*m+1),
      ∀lam : ℝ, ∀z A : ℂ, ∀rootB : ℂ→ℂ,
      ‖t‖<r → (∀i, ‖d+v i‖<r) → spectralS z≠0 →
      B t=spectralT lam z/spectralS z →
      edgeMapV lam (-1) z=(Real.cos phi:ℂ)+B t*t →
      A^2=spectralProduct lam z → A/spectralS z=rootB t →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      A^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
        continuedAngularDensity lam z (fun i => (Real.pi:ℂ)+d+v i)=
          formFactorNumerator B rootB phi hphi d t v *
            cothHalf (fun u => poleEquation B phi hphi d u v) t := by
  obtain ⟨r,hr,hroot⟩ := negativePhase_root_uniform B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m d t v lam z A rootB ht hv hS hB he hA hAR hres
  have hR : rootB t^2=B t := by
    rw [←hAR,paper_rootB_sq hS hA,←hB]
  apply scaled_continuedAngularDensity_eq_phase m B rootB phi hphi d t v hB hAR hR _ hres
  intro i
  rw [show (Real.pi:ℂ)+d+v i=(Real.pi:ℂ)+(d+v i) by ring,
    continuedTransferRoot_eq_negativeDispersion B hB he]
  exact hroot t (d+v i) ht (hv i)

end IsingBulk.Anisotropic.NegativeCycles
