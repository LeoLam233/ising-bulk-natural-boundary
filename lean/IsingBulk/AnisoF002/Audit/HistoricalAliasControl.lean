import IsingBulk.Anisotropic.NegativeNormalForm.UniformExactNormalForm
import IsingBulk.AnisoF002.Audit.RouteCheck

/-!
# External negative control: actual historical exact-normal-form alias

This module is an audit fixture and is absent from the F002 mathematical root.
It invokes the actual completed C001 dimension-uniform exact pole normal form,
which REUSE_AND_ROUTE_POLICY explicitly forbids as a substitute for F002's new
negative-HT derivation. The checker must reject this stored proof and its alias.
No result here is offered as new F002 mathematical progress. This control tests
the specified prohibited core endpoint; it does not claim a replay/control of
the historical final natural-boundary theorem.
-/
namespace AnisoF002NegativeControl
open IsingBulk.Anisotropic.NegativeNormalForm
open Set Metric Filter
open scoped Topology

theorem historical_alias (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ δ R r C : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<C ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness B phi hphi n d r C,
      ∃ J : UniformCorrectionWitness B phi hphi n d r C P R,
        AnalyticOnNhd ℂ (fun y => P.V (J.W y)) (ball 0 δ) ∧ P.V (J.W 0)=0 ∧
        HasFDerivAt (fun y => P.V (J.W y)) (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
        (∀ e y, P.V (J.W (permute e y))=permute e (P.V (J.W y))) ∧
        (∀ y, ‖y‖≤δ → ‖P.V (J.W y)‖≤4*‖y‖ ∧ ‖P.V (J.W y)-y‖≤(3/32)*‖y‖ ∧
          (ZeroMean y → ZeroMean (P.V (J.W y)) ∧
            P.T (P.V (J.W y))=1-Complex.cos d+centralHessian B phi d/(2*n)*quadratic y)) :=
  IsingBulk.Anisotropic.NegativeNormalForm.exists_dimension_uniform_exact_normal_form
    B phi hphi hB hB0

end AnisoF002NegativeControl

set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  AnisoF002Audit.assertHistoricalRejected
    `AnisoF002NegativeControl.historical_alias
    `IsingBulk.Anisotropic.NegativeNormalForm.exists_dimension_uniform_exact_normal_form
