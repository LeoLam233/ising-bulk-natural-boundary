import IsingBulk.Anisotropic.NegativeNormalForm.JointFactorIdentification

namespace IsingBulk.Joint.Negative
noncomputable section
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

/-- Joint analytic factors identify actual iterated divided differences, including coincidences. -/
theorem joint_double_dslope_eq_of_factorization_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ → ℂ) (A H : E × ℂ → ℂ) (a : E)
    (hA : AnalyticAt ℂ A (a,0)) (hH : AnalyticAt ℂ H (a,0))
    (he : ∀ᶠ p : E × ℂ in 𝓝 (a,0),
      f p.1 p.2-f p.1 0=p.2*A p ∧ A p-A (p.1,0)=p.2*H p) :
    ∀ᶠ p : E × ℂ in 𝓝 (a,0), dslope (dslope (f p.1) 0) 0 p.2=H p := by
  rw [nhds_prod_eq] at he
  obtain ⟨pa,hpa,pb,hpb,he⟩ := Filter.eventually_prod_iff.mp he
  have ht0 : ContinuousAt (fun p : E × ℂ => (p.1,(0:ℂ))) (a,0) :=
    continuousAt_fst.prodMk continuousAt_const
  have hAe := ht0.tendsto.eventually hA.eventually_analyticAt
  have hHe := ht0.tendsto.eventually hH.eventually_analyticAt
  have hrect : ∀ᶠ p : E × ℂ in 𝓝 (a,0), pa p.1 ∧ pb p.2 := by
    rw [nhds_prod_eq]
    exact Filter.eventually_prod_iff.mpr ⟨pa,hpa,pb,hpb,fun {_} hx {_} hy => ⟨hx,hy⟩⟩
  filter_upwards [hrect,hAe,hHe] with p hp hAp hHp
  have hAv : AnalyticAt ℂ (fun v => A (p.1,v)) 0 :=
    hAp.comp (f := fun v : ℂ => (p.1,v)) (analyticAt_const.prod analyticAt_id)
  have hHv : AnalyticAt ℂ (fun v => H (p.1,v)) 0 :=
    hHp.comp (f := fun v : ℂ => (p.1,v)) (analyticAt_const.prod analyticAt_id)
  exact double_dslope_eq_of_factorization hpb hAv hHv
    (fun v hv => (he hp.1 hv).1) (fun v hv => (he hp.1 hv).2) p.2 hp.2

end
end IsingBulk.Joint.Negative
