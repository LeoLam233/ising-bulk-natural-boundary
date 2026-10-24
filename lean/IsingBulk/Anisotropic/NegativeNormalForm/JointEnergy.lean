import IsingBulk.Anisotropic.NegativeNormalForm.FactorIdentification
import IsingBulk.Anisotropic.NegativeNormalForm.PoleSeparableMap

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology
set_option maxHeartbeats 800000

/-- Identification includes v=0; the derivative value is proved, not assigned. -/
theorem phaseSecondFactor_eq_double_dslope_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    ∀ᶠ z : ℂ × ℂ in 𝓝 (1-Complex.cos d,0),
      dslope (dslope (negativePhase B phi hphi z.1) d) d (d+z.2) =
        phaseSecondFactor B phi hphi d z.1 z.2 := by
  have he := phase_factors_eventually B phi hphi d hB
  rw [nhds_prod_eq] at he
  obtain ⟨pa,hpa,pb,hpb,he⟩ := Filter.eventually_prod_iff.mp he
  have ht0 : ContinuousAt (fun z : ℂ × ℂ => (z.1,(0:ℂ))) (1-Complex.cos d,0) :=
    continuousAt_fst.prodMk continuousAt_const
  have hAe := ht0.tendsto.eventually (phaseFirstFactor_analyticAt B phi hphi d hB).eventually_analyticAt
  have hHe := ht0.tendsto.eventually (phaseSecondFactor_analyticAt B phi hphi d hB).eventually_analyticAt
  have hrect : ∀ᶠ z : ℂ × ℂ in 𝓝 (1-Complex.cos d,0), pa z.1 ∧ pb z.2 := by
    rw [nhds_prod_eq]
    exact Filter.eventually_prod_iff.mpr ⟨pa,hpa,pb,hpb,fun {_} hx {_} hy => ⟨hx,hy⟩⟩
  filter_upwards [hrect,hAe,hHe] with z hz hA hH
  have hAv : AnalyticAt ℂ (fun v => phaseFirstFactor B phi hphi d z.1 v) 0 :=
    hA.comp (f := fun v : ℂ => (z.1,v)) (analyticAt_const.prod analyticAt_id)
  have hHv : AnalyticAt ℂ (fun v => phaseSecondFactor B phi hphi d z.1 v) 0 :=
    hH.comp (f := fun v : ℂ => (z.1,v)) (analyticAt_const.prod analyticAt_id)
  have hident := double_dslope_eq_of_factorization (s := {v | pb v}) hpb hAv hHv
    (f := fun v => negativePhase B phi hphi z.1 (d+v))
    (fun v hv => by simpa only [add_zero,phaseIncrement] using (he hz.1 hv).1)
    (fun v hv => (he hz.1 hv).2) z.2 hz.2
  simpa only [double_dslope_translate] using hident

/-- Joint analyticity of the actual angular energy quotient with varying anisotropy. -/
theorem energyQuotient_joint_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d h : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (c : ℂ → ℂ) (hc : AnalyticAt ℂ c (1-Complex.cos d)) (hc0 : c (1-Complex.cos d) ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ =>
      energyQuotient (negativePhase B phi hphi z.1) (deriv (negativePhase B phi hphi z.1) d)
        d h (c z.1) z.2) (1-Complex.cos d,0) := by
  by_cases hh : h=0
  · simp only [hh, energyQuotient, zero_mul, div_zero, ite_self]
    exact analyticAt_const
  have hc' : AnalyticAt ℂ (fun z : ℂ × ℂ => -2/(h*c z.1)) (1-Complex.cos d,0) :=
    analyticAt_const.div (analyticAt_const.mul (hc.comp (f := fun z : ℂ × ℂ => z.1) analyticAt_fst)) (mul_ne_zero hh hc0)
  have hmodel := hc'.mul (phaseSecondFactor_analyticAt B phi hphi d hB)
  have hg := negativePhase_analyticAt_center B phi hphi d hB
  have ht : ContinuousAt (fun z : ℂ × ℂ => (z.1,d)) (1-Complex.cos d,0) :=
    continuousAt_fst.prodMk continuousAt_const
  have hge := ht.tendsto.eventually hg.eventually_analyticAt
  apply hmodel.congr
  filter_upwards [phaseSecondFactor_eq_double_dslope_eventually B phi hphi d hB,hge] with z hz hgz
  have hgz' : AnalyticAt ℂ (negativePhase B phi hphi z.1) d :=
    hgz.comp (f := fun v : ℂ => (z.1,v)) (analyticAt_const.prod analyticAt_id)
  rw [energyQuotient_eq_double_dslope hgz',hz]
  rfl

end
end IsingBulk.Anisotropic.NegativeNormalForm
