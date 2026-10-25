import IsingBulk.Joint.Negative.RestrictedPeriod
import IsingBulk.Joint.Negative.UpperChart
import IsingBulk.Joint.Negative.JetPartition
import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterCauchy
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

import IsingBulk.Anisotropic.RegularEdges.LocalFourthRoot

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open Set Filter Metric MeasureTheory RegularEdges NegativeCycles
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- Actual restricted physical outer coefficients, with the SAME original
upper chart and paper reparametrization. No whole-period equality is used in
place of the restricted density identity. -/
theorem physical_outer_jet_cauchy {b : ℝ} {Z : ℂ→Coupling} {amp f : ℂ→ℂ} {r0 : ℝ}
    (_hr0 : 0<r0) (hZ : AnalyticAt ℂ Z 0) (hA : AnalyticAt ℂ amp 0) (hA0 : amp 0≠0)
    (hS0 : IsingBulk.Joint.S (Z 0)≠0)
    (hedge : IsingBulk.Joint.A (Z 0)+T (Z 0)=(b:ℂ)*IsingBulk.Joint.S (Z 0))
    (hb : |b|<1) (hB0 : 0<(negativeChartB Z 0).im)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (hdata : ∀u∈upperBall r0,transferC (Z u)+transferB (Z u)=(b:ℂ)+u ∧
      0<(negativeChartB Z u).im)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0,f (-(ε:ℂ))∈upperBall r0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀n j : ℕ,Odd (n+1) →
      ‖∫v in physicalOuterRegion n σ,
        physicalDensityTaylor n (fun t=>Z (f t)) (fun t=>amp (f t)) j v‖≤
        K*particleEdgeMajorant r C M (n+1)*(((n+1:ℕ):ℝ)/a)^j := by
  let B := negativeChartB Z
  let S := negativeChartS Z
  have hBa : AnalyticAt ℂ B 0 := negativeChartB_analyticAt hZ hS0
  have hSa : AnalyticAt ℂ S 0 := negativeChartS_analyticAt hZ
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcb⟩ := outer_negative_actual_jet_cauchy
    hb hB0 hBa (hSa.div hA hA0) (div_ne_zero hS0 hA0) hf hf0 σ hσ
  refine ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,?_⟩
  intro n j hn
  let E := physicalOuterRegion n σ
  have hE : MeasurableSet E := measurableSet_Icc.inter
    (measurableSet_le measurable_const (physicalShiftedEnergy_measurable n))
  have hsub : E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi) := fun _ hv=>hv.1
  let F : ℂ→ℂ := fun t=>∫v in E,weightedShiftedPhysicalDensity n
    (fun u=>Z (f u)) (fun u=>amp (f u)) v t
  let G : ℂ→ℂ := fun t=>outerNegativePeriod b B (fun u=>S u/amp u) n E (fun _=>1) (f t)
  have hZf := hZ.fun_comp_of_eq (f := f) hf hf0
  have hAf := hA.fun_comp_of_eq (f := f) hf hf0
  obtain ⟨rp,hrp,hphysical⟩ := weightedShiftedPhysicalDensity_restricted_jets n hn hZf hAf
    (by simpa only [hf0] using hS0) (by simpa only [hf0] using hedge) hb
    (by simpa only [hf0,negativeChartB] using hB0)
  have hFp := hphysical E hsub
  have hF0 : AnalyticAt ℂ F 0 := hFp.1 0 (mem_ball_self hrp)
  have hboundary := (hFp.2 j 0 (by simpa using hrp)).2
  change iteratedDeriv j F 0/(j.factorial:ℂ)=_ at hboundary
  simp only [physicalDensityTaylor]
  rw [←hboundary]
  have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ=>-(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  let V : Set ℂ := {t | AnalyticAt ℂ f t ∧ f t∈upperBall r0}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.1.eventually_analyticAt.and
      (ht.1.continuousAt.tendsto.eventually ((upperBall_isOpen r0).mem_nhds ht.2))
  have heq : EqOn F G V := by
    intro t ht
    exact weighted_restricted_eq_outerNegativePeriod n (B := B) (S := S) (amp := amp)
      (curve := Z) (u := f t) rfl rfl
      (hdata (f t) ht.2).1 ht.2.2 (hdata (f t) ht.2).2 hE hsub
  have hinside : ∀ᶠ ε : ℝ in 𝓝[>] 0,-(ε:ℂ)∈V := by
    filter_upwards [hin,hpath.eventually hf.eventually_analyticAt] with ε hi ha
    exact ⟨ha,hi⟩
  have hder : ∀ᶠ ε : ℝ in 𝓝[>] 0,iteratedDeriv j F (-(ε:ℂ))=iteratedDeriv j G (-(ε:ℂ)) := by
    filter_upwards [hinside] with ε hε
    have hev : F =ᶠ[𝓝 (-(ε:ℂ))] G := by
      filter_upwards [hV.mem_nhds hε] with t ht
      exact heq ht
    exact hev.iteratedDeriv_eq j
  have hc : ContinuousAt (iteratedDeriv j F) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (hF0.iterated_deriv j).continuousAt
  have hlim := (hc.tendsto.comp hpath).div_const (j.factorial:ℂ)
  apply le_of_tendsto hlim.norm
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖-(ε:ℂ)‖<a/((n+1:ℕ):ℝ) :=
    hpath.norm.eventually (gt_mem_nhds (by simp only [norm_zero]; positivity))
  filter_upwards [hder,hsmall] with ε he hs
  dsimp only [Function.comp_apply]
  rw [he]
  exact (hcb n j E hE (fun _ hv=>hv.2) (fun _=>1) continuous_const
    (fun _ _=>by norm_num) (-(ε:ℂ)) hs).2

end
end IsingBulk.Joint.Negative
