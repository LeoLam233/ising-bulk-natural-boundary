import IsingBulk.HT22.Geometry.InverseJets
import IsingBulk.HT22.Transport.MixedCovariance

/-! The actual F001 unshifted inverse and mixed residual field. The only
excluded denominator is the full mixed covariance, not partial diagonals. -/
namespace IsingBulk.HT22
noncomputable section
open scoped BigOperators Topology
open Geometry

abbrev sourceInverseV := Geometry.inverseV
abbrev sourceInverseT := Geometry.inverseT

def sourceCovariance {N : ℕ} (t : ℂ) (v : Fin N → ℂ) : ℂ :=
  mixedCovariance (fun i => regularInverse t (v i)) (fun i => sourceInverseV t (v i))

def sourceResidual {N : ℕ} (t : ℂ) (v : Fin N → ℂ) : Fin N → ℂ :=
  mixedCollectiveField (fun i => regularInverse t (v i))
    (fun i => sourceInverseV t (v i)) (fun i => sourceInverseT t (v i))

theorem sourceResidual_sum {N : ℕ} (t : ℂ) (v : Fin N → ℂ) :
    (∑ i, sourceResidual t v i)=0 := mixedCollectiveField_sum _ _ _

theorem sourceResidual_constraint {N : ℕ} (t : ℂ) (v : Fin N → ℂ)
    (hR : sourceCovariance t v≠0) :
    (∑ i, sourceInverseV t (v i)*sourceResidual t v i)=-(∑ i, sourceInverseT t (v i)) :=
  mixedCollectiveField_weighted _ _ _ hR

/-- The actual residual is jointly analytic through every partial collision
once the real geometric projected bound excludes its sole denominator. -/
theorem sourceResidual_analyticAt {N : ℕ} (t : ℂ) (v : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v i))
    (hR : sourceCovariance t v≠0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => sourceResidual z.1 z.2) (t,v) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => z.2 i) (t,v) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (t,v))
  have hu (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => regularInverse z.1 (z.2 i)) (t,v) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => regularInverse z.1 z.2) (hU i)
      (analyticAt_fst.prod (hcoord i))
  have hv (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => sourceInverseV z.1 (z.2 i)) (t,v) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => sourceInverseV z.1 z.2)
      (inverseV_joint_analytic t (v i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have hd (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => sourceInverseT z.1 (z.2 i)) (t,v) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => sourceInverseT z.1 z.2)
      (inverseT_joint_analytic t (v i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have hRa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => sourceCovariance z.1 z.2) (t,v) :=
    (Finset.analyticAt_fun_sum Finset.univ (fun i _ =>
      Finset.analyticAt_fun_sum Finset.univ (fun l _ =>
        ((hu i).sub (hu l)).mul ((hv i).sub (hv l))))).div_const
  have hA := (Finset.analyticAt_fun_sum Finset.univ (fun i _ => hd i)).neg
  apply AnalyticAt.pi
  intro i
  exact (hA.fun_div hRa hR).mul
    (Finset.analyticAt_fun_sum Finset.univ (fun l _ => (hu i).sub (hu l)))

end
end IsingBulk.HT22
