import IsingBulk.HT22.Transport.FieldNeighborhood.JetTheorem
import IsingBulk.HT22.Tail.VandermondeTransport
import IsingBulk.Preferred22.CollectiveBounds

/-! Analytic partial-diagonal extension of the new residual pair factor. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

theorem inverse_dslope_joint_analytic (t v w : ℂ)
    (hv : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v))
    (hw : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,w)) :
    AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => dslope (regularInverse z.1.1) z.1.2 z.2)
      ((t,w),v) := by
  let F : (ℂ × ℂ) × ℂ → ℂ := fun z => regularInverse z.1.1 z.2
  have hv' : AnalyticAt ℂ F ((t,w),v) :=
    AnalyticAt.comp (f := fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) hv
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hw' : AnalyticAt ℂ F ((t,w),w) :=
    AnalyticAt.comp (f := fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) hw
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  exact analyticAt_moving_dslope (F := F) (T := fun z : ℂ × ℂ => z.2) hv' hw' analyticAt_snd

theorem residualPairSlope_analyticAt {N : ℕ} (x : SourcePoint N) (i j : Fin N)
    (hU : ∀ a, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 a))
    (hR : sourceCovariance x.1 x.2≠0) :
    AnalyticAt ℂ (fun z : SourcePoint N => residualPairSlope z.1 z.2 i j) x := by
  have hq (a : Fin N) : AnalyticAt ℂ (fun z : SourcePoint N => z.2 a) x :=
    (((ContinuousLinearMap.proj a : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt x)
  have hUt (a : Fin N) : AnalyticAt ℂ (fun z : SourcePoint N => sourceInverseT z.1 (z.2 a)) x :=
    AnalyticAt.comp (f := fun z : SourcePoint N => (z.1,z.2 a))
      (g := fun z : ℂ × ℂ => sourceInverseT z.1 z.2)
      (inverseT_joint_analytic x.1 (x.2 a) (hU a)) (analyticAt_fst.prod (hq a))
  have hCov : AnalyticAt ℂ (fun z : SourcePoint N => sourceCovariance z.1 z.2) x := by
    exact (Finset.univ.analyticAt_fun_sum (fun a _ =>
      Finset.univ.analyticAt_fun_sum (fun b _ =>
        ((sourceInverseCoordinate_analyticAt x a (hU a)).sub
          (sourceInverseCoordinate_analyticAt x b (hU b))).mul
        ((sourceInverseVCoordinate_analyticAt x a (hU a)).sub
          (sourceInverseVCoordinate_analyticAt x b (hU b)))))).div_const
  have hds : AnalyticAt ℂ (fun z : SourcePoint N => dslope (regularInverse z.1) (z.2 j) (z.2 i)) x :=
    AnalyticAt.comp (f := fun z : SourcePoint N => ((z.1,z.2 j),z.2 i))
      (g := fun z : (ℂ × ℂ) × ℂ => dslope (regularInverse z.1.1) z.1.2 z.2)
      (inverse_dslope_joint_analytic x.1 (x.2 i) (x.2 j) (hU i) (hU j))
      ((analyticAt_fst.prod (hq j)).prod (hq i))
  exact (((Finset.univ.analyticAt_fun_sum (fun a _ => hUt a)).neg.div hCov hR).mul analyticAt_const).mul hds

theorem residualPairSlope_norm_bound {N : ℕ} (x : SourcePoint N) (i j : Fin N)
    (A S R : ℝ) (hA : 0≤A) (_hS : 0≤S) (hR : 0<R)
    (hUt : ∀ a, ‖sourceInverseT x.1 (x.2 a)‖≤A)
    (hds : ‖dslope (regularInverse x.1) (x.2 j) (x.2 i)‖≤S)
    (hcov : R≤‖sourceCovariance x.1 x.2‖) :
    ‖residualPairSlope x.1 x.2 i j‖≤A*S*(N:ℝ)^2/R := by
  have hsum : ‖∑ a,sourceInverseT x.1 (x.2 a)‖≤(N:ℝ)*A :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => hUt a))
  unfold residualPairSlope
  rw [norm_mul,norm_mul,norm_div,norm_neg,Complex.norm_natCast]
  calc
    _ ≤ (((N:ℝ)*A)/R)*(N:ℝ)*S :=
      mul_le_mul (mul_le_mul_of_nonneg_right (div_le_div₀ (by positivity) hsum hR hcov) (by positivity))
        hds (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end IsingBulk.HT22
