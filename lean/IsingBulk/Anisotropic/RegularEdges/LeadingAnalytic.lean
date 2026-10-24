import IsingBulk.Anisotropic.RegularEdges.LeadingNumerator
import IsingBulk.Anisotropic.RegularEdges.LeadingParameters

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

def edgeComplexRoot (b : ℝ) (B : ℂ→ℂ) (u q : ℂ) : ℂ :=
  continuedRoot ((b:ℂ)+u+B u*(1-Complex.cos q))

def edgeComplexDenominator {N : ℕ} (b : ℝ) (B : ℂ→ℂ) (p : ℂ×(Fin N→ℂ)) : ℂ :=
  1-∏ i,edgeComplexRoot b B p.1 (p.2 i)

def edgeComplexAmplitude {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (p : ℂ×(Fin N→ℂ)) : ℂ :=
  (B p.1)^(N.choose 2)*(S p.1)⁻¹^N *
    (∏ i,2*edgeComplexRoot b B p.1 (p.2 i)/(1-edgeComplexRoot b B p.1 (p.2 i)^2)) *
    (∏ ij∈firstStrictPairs N, edgeComplexRoot b B p.1 (p.2 ij.1)*edgeComplexRoot b B p.1 (p.2 ij.2)/
      (1-edgeComplexRoot b B p.1 (p.2 ij.1)*edgeComplexRoot b B p.1 (p.2 ij.2))^2) *
    (1+∏ i,edgeComplexRoot b B p.1 (p.2 i))

def edgeSincFactor {N : ℕ} (q : Fin N→ℝ) : ℂ :=
  ∏ p∈firstStrictPairs N,(Real.sinc ((q p.1-q p.2)/2):ℂ)^2

@[simp] theorem edgeComplexRoot_real (b : ℝ) (B : ℂ→ℂ) (u : ℂ) (q : ℝ) :
    edgeComplexRoot b B u (q:ℂ)=edgeParamRoot b B u q := by
  simp [edgeComplexRoot,edgeParamRoot,edgeParamW,Complex.ofReal_cos]

@[simp] theorem edgeComplexRoot_zero (b : ℝ) (B : ℂ→ℂ) :
    edgeComplexRoot b B 0 0=continuedRoot (b:ℂ) := by simp [edgeComplexRoot]

theorem edgeComplexRoot_joint_analyticAt {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (i : Fin N) :
    AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => edgeComplexRoot b B p.1 (p.2 i)) (0,0) := by
  have dq : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => p.2 i) (0,0) :=
    (ContinuousLinearMap.proj i : (Fin N→ℂ)→L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (0,0) := hB.comp (x := ((0,0):ℂ×(Fin N→ℂ))) analyticAt_fst
  exact AnalyticAt.fun_comp_of_eq
    (f := fun p : ℂ×(Fin N→ℂ) => (b:ℂ)+p.1+B p.1*(1-Complex.cos (p.2 i)))
    (g := continuedRoot)
    (continuedRoot_analyticAt (show (b:ℂ)∈continuedRootDomain from Or.inr (by simpa using hb)))
    ((analyticAt_const.add analyticAt_fst).add (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp dq))))
    (by simp)

theorem edgeComplexDenominator_analyticAt {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (@edgeComplexDenominator N b B) (0,0) := by
  exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod
    (fun i _ => edgeComplexRoot_joint_analyticAt hb hB i))

theorem edgeComplexAmplitude_analyticAt {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    AnalyticAt ℂ (@edgeComplexAmplitude N b B S) (0,0) := by
  have dr (i : Fin N) := edgeComplexRoot_joint_analyticAt hb hB i
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (0,0) := hB.comp (x := ((0,0):ℂ×(Fin N→ℂ))) analyticAt_fst
  have dS : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => S p.1) (0,0) := hS.comp (x := ((0,0):ℂ×(Fin N→ℂ))) analyticAt_fst
  have hd : 1-continuedRoot (b:ℂ)^2≠0 := by
    simpa [edgeRoot,edgeW,pow_two] using edgeRoot_pair_denominator_ne_zero hb hBi 0 0
  unfold edgeComplexAmplitude
  refine ((((dB.pow _).mul ((dS.inv hS0).pow _)).mul ?_).mul ?_).mul
    (analyticAt_const.add (Finset.univ.analyticAt_fun_prod (fun i _ => dr i)))
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2)) (by simpa using hd)
  · apply (firstStrictPairs N).analyticAt_fun_prod
    intro p _
    exact ((dr p.1).mul (dr p.2)).div ((analyticAt_const.sub ((dr p.1).mul (dr p.2))).pow 2)
      (by simpa [pow_two] using pow_ne_zero 2 hd)

theorem edgeComplexAmplitude_real {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) :
    edgeRegularAmplitude b B S u q*(1+edgeRootProduct b B u q)=
      edgeSincFactor q*edgeComplexAmplitude b B S (u,fun i => (q i:ℂ)) := by
  simp only [edgeRegularAmplitude,edgeComplexAmplitude,edgeComplexRoot_real,
    edgeSincFactor,edgeRootProduct,Finset.prod_mul_distrib]
  ring

theorem edgeAngularDensity_analytic_factorization {N : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularDensity b B S u q=(firstVandermonde q:ℂ)^2*edgeSincFactor q*
      (edgeComplexAmplitude b B S (u,fun i => (q i:ℂ))/
        edgeComplexDenominator b B (u,fun i => (q i:ℂ))) := by
  rw [edgeAngularDensity_factorization,edgeComplexAmplitude_real]
  simp only [edgeComplexDenominator,edgeComplexRoot_real,edgeRootProduct]
  ring

theorem edgeComplexAmplitude_collision {N : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (hres : continuedRoot (b:ℂ)^N=1) :
    edgeComplexAmplitude b B S (0,(0:Fin N→ℂ))=2*edgeRegularAmplitude b B S 0 (0:Fin N→ℝ) := by
  have h := edgeComplexAmplitude_real b B S 0 (0:Fin N→ℝ)
  simpa [edgeSincFactor,edgeRootProduct,edgeParamRoot,edgeParamW,hres,mul_comm,one_add_one_eq_two] using! h.symm

end
end IsingBulk.Anisotropic.RegularEdges
