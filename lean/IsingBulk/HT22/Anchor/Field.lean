import IsingBulk.HT22.Anchor.FixedCoordinate
import IsingBulk.HT22.Tail.SourcePiola
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- F001's literal named-anchor residual at fixed v. -/
def residualField {N : ℕ} (a : Fin N) (t : ℂ) (v : Fin N → ℂ) : Fin N → ℂ :=
  anchorField (fun i => inverseT t (v i)) (fun i => inverseV t (v i)) a

def angularField {N : ℕ} (a : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  let v := Tail.sourceCoordinate τ p m t θ
  preferredAngularRepresentative (preferredContourMatrix τ p m θ)
    (fun i => inverseT t (v i)) (fun i => inverseV t (v i)) (residualField a t v)

theorem residualField_constraint {N : ℕ} (a : Fin N) (t : ℂ) (v : Fin N → ℂ)
    (ha : inverseV t (v a)≠0) :
    (∑ i,inverseV t (v i)*residualField a t v i)=-(∑ i,inverseT t (v i)) :=
  anchorField_weighted_sum _ _ _ ha

theorem angularField_tangent {N : ℕ} (a : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (hM : (preferredContourMatrix τ p m θ).det≠0)
    (ha : inverseV t (Tail.sourceCoordinate τ p m t θ a)≠0) :
    (∑ i,angularField a τ p m t θ i)=0 :=
  preferredAngularRepresentative_tangent _ _ _ _
    (preferredContourMatrix_column_sum τ p m θ) hM (residualField_constraint a t _ ha)

/-- The new anchor is analytic also at total equality: its only denominator
is the named anchor inverse derivative, never a diameter or covariance. -/
theorem residualField_analyticAt {N : ℕ} (a : Fin N) (t : ℂ) (v : Fin N → ℂ)
    (hU : ∀ i,AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v i))
    (ha : inverseV t (v a)≠0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => residualField a z.1 z.2) (t,v) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => z.2 i) (t,v) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (t,v))
  have hd (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => inverseT z.1 (z.2 i)) (t,v) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => inverseT z.1 z.2)
      (inverseT_joint_analytic t (v i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have hv : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => inverseV z.1 (z.2 a)) (t,v) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 a))
      (g:=fun z : ℂ × ℂ => inverseV z.1 z.2)
      (inverseV_joint_analytic t (v a) (hU a)) (analyticAt_fst.prod (hcoord a))
  apply AnalyticAt.pi
  intro i
  by_cases hi : i=a
  · simp only [residualField,anchorField,hi,ite_true]
    exact (Finset.univ.analyticAt_fun_sum (fun i _ => hd i)).neg.fun_div hv ha
  · simp only [residualField,anchorField,hi,ite_false]
    exact analyticAt_const
end
end IsingBulk.HT22.Anchor
