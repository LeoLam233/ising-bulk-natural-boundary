import IsingBulk.Anisotropic.RegularEdges.LeadingMultiplier
import IsingBulk.Anisotropic.RegularEdges.ScaledPhysicalTail

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour FormFactors Set Filter Metric MeasureTheory
open scoped Topology

section Chart
variable {lam b : ℝ} {U : Set ℂ} {zeta B S : ℂ→ℂ}
variable (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
  (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0)
  (hB : ∀u∈U,B u=spectralT lam (zeta u)/spectralS (zeta u))
  (hS : ∀u∈U,S u=spectralS (zeta u))
  (he : ∀u∈U,edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
  (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im)
  (hlam : 0<lam) (hphysical : ∀u∈U,zeta u∈(omegaH lam\{0})∪omegaL lam)
include hU ha hz hs hB hS he hup hBi hlam hphysical

theorem unscaledPhysicalCoefficient_fullJet_eq (n j : ℕ) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) u=
      edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n := n) b B S j u := by
  have heq : (fun v => unscaledFullCoefficient (n+1) lam (zeta v))=ᶠ[𝓝 u]
      (fun v => unscaledAngularCoefficient n lam (zeta v)) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact unscaledFullCoefficient_eq_angular_physical n hlam (hphysical v hv)
  rw [heq.iteratedDeriv_eq j]
  exact unscaledAngularCoefficient_fullJet_eq hU ha hz hs hB hS he hup hBi n j hu

theorem physicalCoefficient_scaled_limit_of_full {n j a : ℕ} {C : ℂ}
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    (hlim : Tendsto (fun t : ℝ => (t^a) • edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv j (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (edgeCoefficientNormalization n*C)) := by
  apply (hlim.const_mul (edgeCoefficientNormalization n)).congr'
  filter_upwards [hin] with t ht
  rw [unscaledPhysicalCoefficient_fullJet_eq hU ha hz hs hB hS he hup hBi hlam hphysical n j ht,
    mul_smul_comm]

theorem weightedPhysicalCoefficient_first_leading_limit {n k a : ℕ} (ha' : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    (hb : |b|<1) (hBa : AnalyticAt ℂ B 0) (hBi0 : 0<(B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    {g : ℂ→ℂ} (hg : AnalyticAt ℂ g 0) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k
      (fun v => g v*unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (g 0*edgeCoefficientLeading n k b B S)) := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hf : ∀ᶠ t : ℝ in 𝓝[>] 0,AnalyticAt ℂ
      (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2) := by
    filter_upwards [hin] with t ht
    exact (unscaledFullCoefficient_analyticOnNhd (n+1) (by omega) lam _ (hz _ ht)).comp (ha _ ht)
  apply analytic_multiplier_scaled_jet_limit htend hg hf
  · exact physicalCoefficient_scaled_limit_of_full hU ha hz hs hB hS he hup hBi hlam hphysical hin
      (edgeFullDerivativeIntegral_leading_limit ha' hbalance hmajorant hb hBa hBi0 hSa hS0 hres)
  · intro j hj
    simpa only [mul_zero] using physicalCoefficient_scaled_limit_of_full hU ha hz hs hB hS he hup hBi hlam hphysical hin
      (edgeFullDerivativeIntegral_lower_limit ha' hj hbalance hmajorant hb hBa hBi0 hSa hS0 hres)

theorem weightedPhysicalCoefficient_scaled_zero_of_bounds {n k a : ℕ} (ha' : 0<a)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
    (hbound : ∀j≤k,∃C : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2)‖≤C)
    {g : ℂ→ℂ} (hg : AnalyticAt ℂ g 0) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv k
      (fun v => g v*unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hf : ∀ᶠ t : ℝ in 𝓝[>] 0,AnalyticAt ℂ
      (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2) := by
    filter_upwards [hin] with t ht
    exact (unscaledFullCoefficient_analyticOnNhd (n+1) (by omega) lam _ (hz _ ht)).comp (ha _ ht)
  have hj (j : ℕ) (hjk : j≤k) : Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv j (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using physicalCoefficient_scaled_limit_of_full hU ha hz hs hB hS he hup hBi hlam hphysical hin
      (bounded_jet_scaled_zero ha' (hbound j hjk))
  simpa only [mul_zero] using analytic_multiplier_scaled_jet_limit htend hg hf (hj k le_rfl)
    (fun j hjk => hj j hjk.le)

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
