import IsingBulk.Tail.MicrocoreWeightedStep
import IsingBulk.Analysis.JetsFiniteSum

/-! Finite actual microcore Lie terms, with parameter-only regular derivatives
and real cutoff derivatives recorded separately. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators ContDiff

structure MicrocoreJetTerm (N : ℕ) where
  cutoff : List (Fin N)
  regularPart : ℂ × (Fin N → ℂ) → ℂ

def microParameterDerivative {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) : ℂ := fderiv ℂ F z (1,0)

theorem microParameterDerivative_eq {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) (hF : DifferentiableAt ℂ F z) :
    microParameterDerivative F z = deriv (fun t => F (t,z.2)) z.1 := by
  have hh := hF.hasFDerivAt.comp_hasDerivAt z.1 ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact hh.deriv.symm

def MicrocoreJetTerm.child {N : ℕ} (T : MicrocoreJetTerm N) : Option (Fin N) → MicrocoreJetTerm N
  | none => ⟨T.cutoff,microParameterDerivative T.regularPart⟩
  | some i => ⟨i::T.cutoff,fun z => -regularA z.1 (z.2 i)*T.regularPart z⟩

def microActions (N : ℕ) : List (Option (Fin N)) := none::(List.finRange N).map some

def microcoreJetTerms {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ) : ℕ → List (MicrocoreJetTerm N)
  | 0 => [⟨[],F⟩]
  | j+1 => (microcoreJetTerms F j).flatMap (fun T => (microActions N).map T.child)

def MicrocoreJetTerm.sourceValue {n : ℕ} (T : MicrocoreJetTerm (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ)*chartPullback v θ (fun t φ => T.regularPart (t,φ)) s x

theorem microcoreJetTerms_analytic {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ) (j : ℕ)
    (z : ℂ × (Fin N → ℂ)) (hF : AnalyticAt ℂ F z)
    (hA : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) z) :
    ∀ T ∈ microcoreJetTerms F j, AnalyticAt ℂ T.regularPart z := by
  induction j with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [microcoreJetTerms,List.mem_singleton] using hT
    subst T
    exact hF
  | succ j ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    cases a with
    | none => exact ((ContinuousLinearMap.apply ℂ ℂ (1,0)).analyticAt _).comp (ih P hP).fderiv
    | some i => exact (hA i).neg.mul (ih P hP)

theorem MicrocoreJetTerm.source_differentiable {n : ℕ} (T : MicrocoreJetTerm (n+1))
    (v θ : ℝ) (s : ℂ) (x : AngularSpace n) (w : AngularSpace n → ℝ)
    (hw : ContDiff ℝ ∞ w) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x)) :
    DifferentiableAt ℂ (fun t => T.sourceValue v θ w t x) s ∧
    DifferentiableAt ℝ (T.sourceValue v θ w s) x := by
  obtain ⟨hS,hX⟩ := microcore_pullback_differentiable v θ s x
    (fun t φ => T.regularPart (t,φ)) hs hr hi hn hT.differentiableAt
  have hwx := ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) x)
  exact ⟨(differentiableAt_const _).mul hS,
    (Complex.ofRealCLM.hasFDerivAt.comp x hwx.hasFDerivAt).differentiableAt.mul hX⟩

theorem MicrocoreJetTerm.source_step {n : ℕ} (T : MicrocoreJetTerm (n+1))
    (v θ : ℝ) (s : ℂ) (x : AngularSpace n) (w : AngularSpace n → ℝ)
    (hw : ContDiff ℝ ∞ w) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x)) :
    lieStep (microcoreField v θ) (T.sourceValue v θ w) s x =
      ((microActions (n+1)).map (fun a => (T.child a).sourceValue v θ w s x)).sum := by
  have he := microcore_weighted_pullback_step v θ s x (cutoffJet T.cutoff w)
    (fun t φ => T.regularPart (t,φ))
    ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) x) hs hr hi hg hn hT.differentiableAt
  dsimp only [chartPullback] at he
  have hd := microParameterDerivative_eq T.regularPart (s,chartMap v θ s x) hT.differentiableAt
  have hd' : microParameterDerivative T.regularPart (s,fun i => chartPhase s v θ (x i)) =
      deriv (fun t => T.regularPart (t,fun i => chartPhase s v θ (x i))) s := by
    convert! hd using 1
  rw [← hd'] at he
  change lieStep (microcoreField v θ) (fun t y => (cutoffJet T.cutoff w y:ℂ)*
    chartPullback v θ (fun t φ => T.regularPart (t,φ)) t y) s x = _
  simpa [microActions,MicrocoreJetTerm.child,MicrocoreJetTerm.sourceValue,
    cutoffJet,chartPullback,Function.comp_def,List.finRange,List.sum_ofFn,Fin.sum_univ_succ,add_comm] using he

end
end IsingBulk.Tail
