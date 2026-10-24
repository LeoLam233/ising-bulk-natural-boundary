import IsingBulk.Anisotropic.RegularEdges.PositiveChartData
import IsingBulk.Anisotropic.Final.AnalyticFactor

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric FormFactors
open scoped Topology

theorem positive_prime_raw_chart_no_extension {lam b : ℝ} {D : Set ℂ} {zeta : ℂ→ℂ} {r : ℝ}
    (hlam : 0<lam) (hb : |b|<1) (hprime : b∈primePhaseCosines) (hr : 0<r)
    (hza : AnalyticOnNhd ℂ zeta (ball 0 r))
    (hAa : AnalyticOnNhd ℂ (positiveChartRoot lam zeta) (ball 0 r))
    (hd : 0<spectralDet lam (zeta 0))
    (hphysical : D⊆omegaH lam∪omegaL lam)
    (hdata : ∀u∈ball 0 r,0<(positiveChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
      positiveChartRoot lam zeta u≠0 ∧ edgeMapV lam 1 (zeta u)=(b:ℂ)+u ∧
      (0<u.im → zeta u∈D\{0})) :
    (¬HasDomainExtension (upperBall r) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^i*unscaledFullCoefficient (2*i+1) lam (zeta u)) 0) ∧
    (¬HasDomainExtension (upperBall r) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u)) 0) := by
  have h0 : (0:ℂ)∈ball 0 r := mem_ball_self hr
  have hz0 := hza 0 h0
  have hS0 := (hdata 0 h0).2.1
  have hP0 : spectralProduct lam (zeta 0)≠0 :=
    mul_ne_zero hS0 (spectralT_ne_zero_of_det_ne_zero hd.ne')
  have hpU : ∀u∈upperBall r,zeta u∈(omegaH lam\{0})∪omegaL lam := by
    intro u hu
    have hD := (hdata u hu.1).2.2.2.2 hu.2
    rcases hphysical hD.1 with hH | hL
    · exact Or.inl ⟨hH,hD.2⟩
    · exact Or.inr hL
  have hz : ∀u∈upperBall r,zeta u∉spectralSet lam := by
    intro u hu
    rcases hpU u hu with hH | hL
    · exact omegaH_subset_spectral_complement hlam hH.1
    · exact omegaL_subset_spectral_complement hlam hL
  have hAsq : ∀u∈upperBall r,positiveChartRoot lam zeta u^2=spectralProduct lam (zeta u) :=
    fun u _ => localParticleRoot_sq hP0 u
  have hBa := positiveChartB_analyticAt (lam := lam) hz0 hS0
  have hSa := positiveChartS_analyticAt hz0
  constructor
  · exact high_prime_chart_no_extension (upperBall_isOpen r) (hza.mono inter_subset_left)
      (hAa.mono inter_subset_left) hz (fun u hu => (hdata u hu.1).2.1)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun u hu => (hdata u hu.1).2.2.2.1)
      (fun _ hu => hu.2) (fun u hu => (hdata u hu.1).1) hlam hpU hb hBa (hdata 0 h0).1
      hSa hS0 hz0 (hAa 0 h0) (hdata 0 h0).2.2.1 hP0 hAsq (upperBall_inward hr) hprime
  · exact low_prime_chart_no_extension (upperBall_isOpen r) (hza.mono inter_subset_left)
      (hAa.mono inter_subset_left) hz (fun u hu => (hdata u hu.1).2.1)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun u hu => (hdata u hu.1).2.2.2.1)
      (fun _ hu => hu.2) (fun u hu => (hdata u hu.1).1) hlam hpU hb hBa (hdata 0 h0).1
      hSa hS0 hz0 (hAa 0 h0) (hdata 0 h0).2.2.1 hP0 hAsq (upperBall_inward hr) hprime

/-- Removing the actual boundary prefactor is justified by its constructed local continuation. -/
theorem no_extension_product_of_upper_fourth_branch {P f F : ℂ→ℂ} {r : ℝ}
    (hr : 0<r) (hPa : AnalyticAt ℂ P 0) (hP0 : P 0≠0)
    (hf : ContinuousOn f (upperBall r)) (hp : ∀u∈upperBall r,f u^4=P u)
    (hraw : ∀δ : ℝ,0<δ → δ≤r → ¬HasDomainExtension (upperBall δ) F 0) :
    ¬HasDomainExtension (upperBall r) (fun u => f u*F u) 0 := by
  obtain ⟨δ,hδ,hδr,g,hg,hg0,hgf⟩ := exists_upper_fourth_branch_extension hr hPa hP0 hf hp
  intro hext
  have he : HasDomainExtension (upperBall δ) (fun u => f u*F u) 0 := by
    obtain ⟨V,hV,h0V,H,hH,hEq⟩ := hext
    exact ⟨V,hV,h0V,H,hH,fun u hu => hEq ⟨hu.1,ball_subset_ball hδr hu.2.1,hu.2.2⟩⟩
  apply hraw δ hδ hδr
  apply domain_extension_of_analytic_factor (hg 0 (mem_ball_self hδ)) hg0
  apply domain_extension_of_eqOn (f := g*F) (g := fun u => f u*F u) _ he
  intro u hu
  exact congrArg (fun v => v*F u) (hgf hu)

end
end IsingBulk.Anisotropic.RegularEdges
