import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets
import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.RegularEdges.LeadingFinite

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def familyEdgeAmplitude {N : ℕ} (b : ℝ) (B S : ℂ × E → ℂ)
    (p : ℂ × (E × (Fin N → ℂ))) : ℂ :=
  edgeComplexAmplitude b (fun u => B (u,p.2.1)) (fun u => S (u,p.2.1)) (p.1,p.2.2)

def familyEdgeDenominator {N : ℕ} (b : ℝ) (B : ℂ × E → ℂ)
    (p : ℂ × (E × (Fin N → ℂ))) : ℂ :=
  edgeComplexDenominator b (fun u => B (u,p.2.1)) (p.1,p.2.2)

def familyEdgeJet {N : ℕ} (b : ℝ) (B S : ℂ × E → ℂ) (j : ℕ)
    (p : ℂ × (E × (Fin N → ℂ))) : ℂ :=
  edgeAnalyticJet b (fun u => B (u,p.2.1)) (fun u => S (u,p.2.1)) j (p.1,p.2.2)

theorem familyEdgeRoot_analyticAt_real {N : ℕ} {b : ℝ} {B : ℂ × E → ℂ}
    {eta : E} (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta))
    (hBi : 0<(B (0,eta)).im) (q : Fin N→ℝ) (i : Fin N) :
    AnalyticAt ℂ (fun p : ℂ × (E × (Fin N→ℂ)) =>
      edgeComplexRoot b (fun u => B (u,p.2.1)) p.1 (p.2.2 i)) (0,(eta,fun k => (q k:ℂ))) := by
  have dq : AnalyticAt ℂ (fun p : ℂ × (E × (Fin N→ℂ)) => p.2.2 i) (0,(eta,fun k => (q k:ℂ))) :=
    (ContinuousLinearMap.proj i : (Fin N→ℂ)→L[ℂ] ℂ).analyticAt _ |>.comp
      (analyticAt_snd.comp analyticAt_snd)
  have dB : AnalyticAt ℂ (fun p : ℂ × (E × (Fin N→ℂ)) => B (p.1,p.2.1))
      (0,(eta,fun k => (q k:ℂ))) := hB.comp
    (f := fun p : ℂ × (E × (Fin N→ℂ)) => (p.1,p.2.1))
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
  exact AnalyticAt.fun_comp_of_eq
    (f := fun p : ℂ × (E × (Fin N→ℂ)) => (b:ℂ)+p.1+B (p.1,p.2.1)*(1-Complex.cos (p.2.2 i)))
    (g := continuedRoot) (continuedRoot_analyticAt (edgeW_domain hb hBi (q i)))
    ((analyticAt_const.add analyticAt_fst).add
      (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp dq))))
    (by simp [edgeW,Complex.ofReal_cos])

theorem familyEdgeDenominator_analyticAt_real {N : ℕ} {b : ℝ} {B : ℂ × E → ℂ}
    {eta : E} (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta))
    (hBi : 0<(B (0,eta)).im) (q : Fin N→ℝ) :
    AnalyticAt ℂ (familyEdgeDenominator (N:=N) b B) (0,(eta,fun k => (q k:ℂ))) := by
  exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod
    (fun i _ => familyEdgeRoot_analyticAt_real hb hB hBi q i))

theorem familyEdgeAmplitude_analyticAt_real {N : ℕ} {b : ℝ} {B S : ℂ × E → ℂ}
    {eta : E} (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta)) (hBi : 0<(B (0,eta)).im)
    (hS : AnalyticAt ℂ S (0,eta)) (hS0 : S (0,eta)≠0) (q : Fin N→ℝ) :
    AnalyticAt ℂ (familyEdgeAmplitude (N:=N) b B S) (0,(eta,fun k => (q k:ℂ))) := by
  have dr (i : Fin N) := familyEdgeRoot_analyticAt_real hb hB hBi q i
  have dB : AnalyticAt ℂ (fun p : ℂ × (E × (Fin N→ℂ)) => B (p.1,p.2.1))
      (0,(eta,fun k => (q k:ℂ))) := hB.comp
    (f := fun p : ℂ × (E × (Fin N→ℂ)) => (p.1,p.2.1))
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
  have dS : AnalyticAt ℂ (fun p : ℂ × (E × (Fin N→ℂ)) => S (p.1,p.2.1))
      (0,(eta,fun k => (q k:ℂ))) := hS.comp
    (f := fun p : ℂ × (E × (Fin N→ℂ)) => (p.1,p.2.1))
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
  have hd (i k : Fin N) :
      1-edgeComplexRoot b (fun u=>B (u,eta)) 0 (q i:ℂ)*
        edgeComplexRoot b (fun u=>B (u,eta)) 0 (q k:ℂ)≠0 := by
    simpa using edgeRoot_pair_denominator_ne_zero hb hBi (q i) (q k)
  unfold familyEdgeAmplitude edgeComplexAmplitude
  refine ((((dB.pow _).mul ((dS.inv hS0).pow _)).mul ?_).mul ?_).mul
    (analyticAt_const.add (Finset.univ.analyticAt_fun_prod (fun i _ => dr i)))
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hd i i)
  · apply (firstStrictPairs N).analyticAt_fun_prod
    intro p _
    exact ((dr p.1).mul (dr p.2)).div ((analyticAt_const.sub ((dr p.1).mul (dr p.2))).pow 2)
      (pow_ne_zero 2 (hd p.1 p.2))

theorem familyEdgeJet_analyticAt_real {N : ℕ} {b : ℝ} {B S : ℂ × E → ℂ}
    {eta : E} (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta)) (hBi : 0<(B (0,eta)).im)
    (hS : AnalyticAt ℂ S (0,eta)) (hS0 : S (0,eta)≠0) (q : Fin N→ℝ) (j : ℕ) :
    AnalyticAt ℂ (familyEdgeJet (N:=N) b B S j) (0,(eta,fun k => (q k:ℂ))) :=
  quotientJetNumerator_joint_analyticAt
    (familyEdgeAmplitude_analyticAt_real hb hB hBi hS hS0 q)
    (familyEdgeDenominator_analyticAt_real hb hB hBi q) j

end
end IsingBulk.Joint.RegularEdges
