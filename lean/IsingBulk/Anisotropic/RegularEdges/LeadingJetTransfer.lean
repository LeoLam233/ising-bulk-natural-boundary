import IsingBulk.Anisotropic.RegularEdges.LeadingPhysical

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Filter MeasureTheory
open scoped Topology

section Chart
variable {n : ℕ} {b : ℝ} {U : Set ℂ} {B S F : ℂ→ℂ}
variable (hfa : AnalyticOnNhd ℂ F U)
  (hJet : ∀j u,u∈U → iteratedDeriv j F u=edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n := n) b B S j u)
include hfa hJet

omit hfa in
theorem coefficient_scaled_limit_of_full_jets {j a : ℕ} {C : ℂ}
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    (hlim : Tendsto (fun t : ℝ => (t^a) • edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv j F (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (edgeCoefficientNormalization n*C)) := by
  apply (hlim.const_mul (edgeCoefficientNormalization n)).congr'
  filter_upwards [hin] with t ht
  rw [hJet j _ ht,
    mul_smul_comm]

theorem weightedCoefficient_first_limit_of_jets {k a : ℕ} (ha' : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    (hb : |b|<1) (hBa : AnalyticAt ℂ B 0) (hBi0 : 0<(B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    {g : ℂ→ℂ} (hg : AnalyticAt ℂ g 0) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k
      (fun v => g v*F v) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (g 0*edgeCoefficientLeading n k b B S)) := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hf : ∀ᶠ t : ℝ in 𝓝[>] 0,AnalyticAt ℂ
      F (Complex.I*(t:ℂ)^2) := by
    filter_upwards [hin] with t ht
    exact hfa _ ht
  apply analytic_multiplier_scaled_jet_limit htend hg hf
  · exact coefficient_scaled_limit_of_full_jets hJet hin
      (edgeFullDerivativeIntegral_leading_limit ha' hbalance hmajorant hb hBa hBi0 hSa hS0 hres)
  · intro j hj
    simpa only [mul_zero] using coefficient_scaled_limit_of_full_jets hJet hin
      (edgeFullDerivativeIntegral_lower_limit ha' hj hbalance hmajorant hb hBa hBi0 hSa hS0 hres)

theorem weightedCoefficient_zero_of_full_bounds {k a : ℕ} (ha' : 0<a)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    (hbound : ∀j≤k,∃C : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2)‖≤C)
    {g : ℂ→ℂ} (hg : AnalyticAt ℂ g 0) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k
      (fun v => g v*F v) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hf : ∀ᶠ t : ℝ in 𝓝[>] 0,AnalyticAt ℂ
      F (Complex.I*(t:ℂ)^2) := by
    filter_upwards [hin] with t ht
    exact hfa _ ht
  have hj (j : ℕ) (hjk : j≤k) : Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv j F (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using coefficient_scaled_limit_of_full_jets hJet hin
      (bounded_jet_scaled_zero ha' (hbound j hjk))
  simpa only [mul_zero] using analytic_multiplier_scaled_jet_limit htend hg hf (hj k le_rfl)
    (fun j hjk => hj j hjk.le)

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
