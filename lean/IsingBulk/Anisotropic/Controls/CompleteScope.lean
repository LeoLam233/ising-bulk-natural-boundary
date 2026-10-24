import IsingBulk.Anisotropic.Final.FullTheorem
import IsingBulk.Anisotropic.Final.IsotropicTheorem
import IsingBulk.Anisotropic.Final.IsotropicHighReal
import IsingBulk.Anisotropic.Final.IsotropicLowReal
import IsingBulk.Anisotropic.NegativeDominance.FixedParticleContinuation
import IsingBulk.Anisotropic.NegativeDominance.PaperModelData

noncomputable section
namespace IsingBulk.Anisotropic.Controls
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open FormFactors NegativeDominance RegularEdges Set Filter
open scoped Topology BigOperators

/-- Definition-level scope check: the HT target is the full, weighted infinite
odd series, including its one-particle term, not a selected or truncated sum. -/
theorem high_target_complete_series (lam : ℝ) (z : ℂ) :
    highNormalizedBulk lam z=highPrefactor lam z*
      ∑'n : ℕ,spectralProduct lam z^n*unscaledFullCoefficient (2*n+1) lam z := rfl

/-- The connected LT target contains every positive even particle order and
starts at two particles, with no zero-particle magnetization term. -/
theorem low_target_complete_connected_series (lam : ℝ) (z : ℂ) :
    lowNormalizedBulk lam z=lowPrefactor lam z*
      ∑'n : ℕ,spectralProduct lam z^(n+1)*unscaledFullCoefficient (2*n+2) lam z := rfl

theorem no_odd_particle_order_omitted {N : ℕ} (hN : Odd N) :
    ∃!n : ℕ,2*n+1=N := by
  obtain ⟨n,hn⟩ := hN
  refine ⟨n,hn.symm,?_⟩
  intro m hm
  omega

theorem no_positive_even_particle_order_omitted {N : ℕ} (hN : Even N) (hpos : 0<N) :
    ∃!n : ℕ,2*n+2=N := by
  obtain ⟨k,hk⟩ := hN
  refine ⟨k-1,by omega,?_⟩
  intro n hn
  omega

/-- Full-lattice scope negative control: an axis-site contribution is retained
by the actual covariance definition but lost by a diagonal-only replacement.
This is a synthetic definition test, not a claimed Gibbs correlation. -/
theorem full_lattice_not_diagonal_control (x : ℝ) :
    highCovarianceSum (fun _ v=>if v=(1,0) then 1 else 0) x=1 ∧
      (∑'k : ℤ,if ((k,k):LatticeSite)=(1,0) then (1:ℝ) else 0)=0 := by
  classical
  constructor
  · simp [highCovarianceSum]
  · have hn (k : ℤ) : ((k,k):LatticeSite)≠(1,0) := by
      intro he
      have hh := Prod.mk.inj he
      omega
    simp [hn]

/-- The actual fixed-particle continuation is analytic for every member of
an arbitrary finite subset, including subsets that omit internal orders. -/
theorem finite_actual_odd_period_analytic {lam b : ℝ} {zeta A : ℂ→ℂ}
    (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (I : Finset ℕ) :
    AnalyticAt ℂ (fun t=>∑n∈I,A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0 := by
  have hn (n : ℕ) : AnalyticAt ℂ (fun t=>A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0 :=
    (hA.pow _).mul ((continuedAngularCoefficient_negative_analyticAt (2*n)
      ⟨n,by omega⟩ hS hedge hb hB).comp hzeta)
  convert I.analyticAt_sum (fun n _=>hn n) using 1
  funext t
  simp only [Finset.sum_apply]

/-- Substantive negative control: every finite replacement of the actual
odd-particle boundary coefficients has strictly positive Taylor radius.
Thus a finite-particle surrogate cannot pass the zero-radius declaration. -/
theorem finite_actual_odd_coefficients_radius_pos {lam b : ℝ} {zeta A : ℂ→ℂ}
    (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (I : Finset ℕ) :
    0<(FormalMultilinearSeries.ofScalars ℂ
      (fun j=>∑n∈I,negativePaperParticleCoefficient lam zeta A n j)).radius := by
  have hf := finite_actual_odd_period_analytic hzeta hA hS hedge hb hB I
  have hn (n : ℕ) : AnalyticAt ℂ (fun t=>A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0 :=
    (hA.pow _).mul ((continuedAngularCoefficient_negative_analyticAt (2*n)
      ⟨n,by omega⟩ hS hedge hb hB).comp hzeta)
  have he : (fun j=>∑n∈I,negativePaperParticleCoefficient lam zeta A n j)=
      (fun j=>iteratedDeriv j (fun t=>∑n∈I,A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0/(j.factorial:ℂ)) := by
    funext j
    rw [iteratedDeriv_fun_sum (fun n _=>(hn n).contDiffAt)]
    simp only [negativePaperParticleCoefficient,Finset.sum_div]
  rw [he]
  exact hf.hasFPowerSeriesAt.radius_pos

/-- The full zero-radius coefficient identity rejects every finite selected
set, not merely a fixed initial truncation or an empty model. -/
theorem full_zero_radius_rejects_finite_particle_identity {lam b : ℝ} {zeta A : ℂ→ℂ}
    (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hfull : (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient lam zeta A)).radius=0)
    (I : Finset ℕ) :
    negativePaperCoefficient lam zeta A≠(fun j=>∑n∈I,negativePaperParticleCoefficient lam zeta A n j) := by
  intro he
  have hp := finite_actual_odd_coefficients_radius_pos hzeta hA hS hedge hb hB I
  rw [←he,hfull] at hp
  exact (lt_irrefl 0) hp

/-- Exact lambda-one correspondence uses the previously verified complete
isotropic HT bulk, not just its first coefficient. -/
theorem lambda_one_full_high_correspondence {x : ℝ} (hx : 0<x) (hxc : x<criticalPoint 1) :
    highNormalizedBulk 1 (x:ℂ)=IsingBulk.HT.Final.interiorFullBulk (Real.sinh x:ℂ) :=
  isotropic_high_real_eq hx hxc

/-- Exact lambda-one LT correspondence retains the connected infinite bulk. -/
theorem lambda_one_full_low_correspondence {x : ℝ} (hx : criticalPoint 1<x)
    {corrH corrL : ℝ→LatticeSite→ℝ} (hphys : PublishedRealSpinFormFactors 1 corrH corrL) :
    lowNormalizedBulk 1 (x:ℂ)=exteriorNormalizedBulk (Real.sinh x:ℂ) :=
  isotropic_low_real_eq hx hphys

/-- Compile-time public-signature checks: positive anisotropy and the published
real spin input suffice, without an analytic endpoint or dominance premise. -/
example {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ→LatticeSite→ℝ} (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    FullPhysicalConclusion J lam corrH corrL := full_physical_conclusion hJ hlam hphys

example {J : ℝ} (hJ : 0<J) {corrH corrL : ℝ→LatticeSite→ℝ}
    (hphys : PublishedRealSpinFormFactors 1 corrH corrL) : FullPhysicalConclusion J 1 corrH corrL :=
  full_physical_conclusion hJ (by norm_num) hphys


example {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ→LatticeSite→ℝ} {mH mL : ℝ→ℝ→ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PhysicalField.PublishedRealGibbsFields J lam corrH corrL mH mL) :
    FullUniformFieldConclusion J lam corrH corrL mH mL :=
  full_uniform_field_conclusion hJ hlam hphys hG

end IsingBulk.Anisotropic.Controls
