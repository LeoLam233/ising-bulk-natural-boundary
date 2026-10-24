import IsingBulk.Anisotropic.RegularEdges.LeadingAway
import IsingBulk.Anisotropic.RegularEdges.LeadingCoefficient
import IsingBulk.Anisotropic.NegativeDominance.GapComposedControl
import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles
import IsingBulk.First.CompactIntegralHolomorphic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

theorem edgeComplexRoot_joint_analyticAt_of_domain {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    {u : ℂ} (hB : AnalyticAt ℂ B u) (q : Fin N→ℝ) (i : Fin N)
    (hdom : edgeParamW b B u (q i)∈continuedRootDomain) :
    AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => edgeComplexRoot b B p.1 (p.2 i))
      (u,fun k => (q k:ℂ)) := by
  have dq : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => p.2 i) (u,fun k => (q k:ℂ)) :=
    (ContinuousLinearMap.proj i : (Fin N→ℂ)→L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (u,fun k => (q k:ℂ)) :=
    hB.comp (x := ((u,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  exact AnalyticAt.fun_comp_of_eq
    (f := fun p : ℂ×(Fin N→ℂ) => (b:ℂ)+p.1+B p.1*(1-Complex.cos (p.2 i)))
    (g := continuedRoot) (continuedRoot_analyticAt hdom)
    ((analyticAt_const.add analyticAt_fst).add
      (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp dq))))
    (by simp [edgeParamW,Complex.ofReal_cos])

theorem edgeComplexAmplitude_analyticAt_of_domain {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    {u : ℂ} (hB : AnalyticAt ℂ B u) (hS : AnalyticAt ℂ S u) (hS0 : S u≠0)
    (q : Fin N→ℝ) (hdom : ∀i,edgeParamW b B u (q i)∈continuedRootDomain)
    (hd : ∀i k,1-edgeParamRoot b B u (q i)*edgeParamRoot b B u (q k)≠0) :
    AnalyticAt ℂ (@edgeComplexAmplitude N b B S) (u,fun k => (q k:ℂ)) ∧
    AnalyticAt ℂ (@edgeComplexDenominator N b B) (u,fun k => (q k:ℂ)) := by
  have dr (i : Fin N) := edgeComplexRoot_joint_analyticAt_of_domain hB q i (hdom i)
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (u,fun k => (q k:ℂ)) :=
    hB.comp (x := ((u,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  have dS : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => S p.1) (u,fun k => (q k:ℂ)) :=
    hS.comp (x := ((u,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  constructor
  · unfold edgeComplexAmplitude
    refine ((((dB.pow _).mul ((dS.inv hS0).pow _)).mul ?_).mul ?_).mul
      (analyticAt_const.add (Finset.univ.analyticAt_fun_prod (fun i _ => dr i)))
    · apply Finset.univ.analyticAt_fun_prod
      intro i _
      exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
        (by simpa only [edgeComplexRoot_real,pow_two] using hd i i)
    · apply (firstStrictPairs N).analyticAt_fun_prod
      intro p _
      exact ((dr p.1).mul (dr p.2)).div ((analyticAt_const.sub ((dr p.1).mul (dr p.2))).pow 2)
        (by simpa only [edgeComplexRoot_real] using pow_ne_zero 2 (hd p.1 p.2))
  · exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod (fun i _ => dr i))

theorem edgeFullIntegrand_eq_analytic_factor {N : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (u : ℂ) (q : Fin N→ℝ) (hd : 1-edgeRootProduct b B u q≠0) :
    edgeFullIntegrand b B S u q=(firstVandermonde q:ℂ)^2*edgeSincFactor q*
      (edgeComplexAmplitude b B S (u,fun i => (q i:ℂ))/
        edgeComplexDenominator b B (u,fun i => (q i:ℂ))) := by
  rw [←edgeAngularDensity_analytic_factorization]
  unfold edgeAngularDensity
  rw [edgeAngularWeight_eq_edgeNumerator]
  unfold edgeFullIntegrand
  field_simp [hd]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
