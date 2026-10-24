import IsingBulk.Anisotropic.NegativeCycles.ActualInnerRemainder
import IsingBulk.Anisotropic.NegativeCycles.PoleTaylorCoefficient
import IsingBulk.Anisotropic.NegativeCycles.FixedDiskCauchyJets

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Filter Metric NegativeNormalForm
open scoped Topology
set_option maxHeartbeats 800000

/-- Literal resonant kernel Taylor coefficients split into the actual residue
coefficient and an explicitly bounded analytic remainder, uniformly before N. -/
theorem exists_actual_inner_taylor (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) :
    ∃ (R₀ : ℂ → ℂ) (r c σ C M : ℝ), 0<r ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ m : ℕ, ∀ v : Config (2*m+1), absoluteEnergy v<σ → ∀ T : ℂ,
      ‖T‖≤r/2 → poleEquation B phi hphi 0 T v=0 → T≠0 → ∀ j : ℕ,
      let R := actualInnerRemainder B rootB phi hphi R₀ m v T
      iteratedDeriv j (fun t => formFactorNumerator B rootB phi hphi 0 t v*
        cothHalf (fun u => poleEquation B phi hphi 0 u v) t) 0/(j.factorial:ℂ)=
        (-2*formFactorNumerator B rootB phi hphi 0 T v/
          poleParameterDerivative B phi hphi 0 T v)/T^(j+1)+
        iteratedDeriv j R 0/(j.factorial:ℂ) ∧
      ‖iteratedDeriv j R 0/(j.factorial:ℂ)‖≤
        (C*remainderGaussianEnvelope M m)/((c/(2*m+1:ℕ))/2)^j := by
  obtain ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,hs⟩ :=
    exists_actual_inner_remainder B rootB phi hphi hB hB0 hrB
  refine ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,?_⟩
  intro m v hv T hT hz hT0 j
  have hh := hs m v hv T hT hz
  have hcN : 0<c/(2*m+1:ℕ) := by positivity
  have hRa := hh.1 0 (by simpa using hcN)
  have he : (fun t => formFactorNumerator B rootB phi hphi 0 t v*
      cothHalf (fun u => poleEquation B phi hphi 0 u v) t) =ᶠ[𝓝 0]
      (fun t => (-2*formFactorNumerator B rootB phi hphi 0 T v/
        poleParameterDerivative B phi hphi 0 T v)/(T-t)+
        actualInnerRemainder B rootB phi hphi R₀ m v T t) := by
    have hb : ∀ᶠ t : ℂ in 𝓝 0, t∈ball 0 (c/(2*m+1:ℕ)) := ball_mem_nhds 0 hcN
    have hn : ∀ᶠ t : ℂ in 𝓝 0, t≠T :=
      continuousAt_id.eventually_ne (Ne.symm hT0)
    filter_upwards [hb,hn] with t ht htT
    rw [hh.2.2.2 t ht htT]
    congr 1
    rw [show T-t=-(t-T) by ring,div_neg]
    ring
  exact ⟨pole_remainder_normalized_taylor _ T hT0 hRa he j,
    analytic_disk_normalized_jet_bound hcN hh.1 hh.2.1 j⟩

end
end IsingBulk.Anisotropic.NegativeCycles
