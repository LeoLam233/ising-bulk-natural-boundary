import IsingBulk.First.PoleDifferentiation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Analytic.Constructions

/-! Joint regularity of the recursively generated pole numerators. A fixed real
shape weight is intentionally kept outside this analytic layer. -/
namespace IsingBulk.First
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def parameterDeriv (F : ℂ × E → ℂ) (p : ℂ × E) : ℂ :=
  deriv (fun s => F (s,p.2)) p.1

/-- Joint analyticity passes to the actual derivative in the first coordinate. -/
theorem parameterDeriv_analyticAt {F : ℂ × E → ℂ} {p : ℂ × E}
    (hF : AnalyticAt ℂ F p) : AnalyticAt ℂ (parameterDeriv F) p := by
  let L : ((ℂ × E) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hg : AnalyticAt ℂ (fun q => fderiv ℂ F q (1,0)) p :=
    (L.analyticAt _).comp hF.fderiv
  apply hg.congr
  obtain ⟨r, hr, hball⟩ := hF.exists_ball_analyticOnNhd
  filter_upwards [ball_mem_nhds p hr] with q hq
  have hsection : HasDerivAt (fun s : ℂ => (s,q.2)) (1,0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have h := (hball q hq).differentiableAt.hasFDerivAt.comp_hasDerivAt q.1 hsection
  exact h.deriv.symm

def jointPoleLeadingNumerator (B D : ℂ × E → ℂ) (k : ℕ) (p : ℂ × E) : ℂ :=
  poleLeadingNumerator (fun s => B (s,p.2)) (fun s => D (s,p.2)) k p.1

def jointPoleRemainder (B D : ℂ × E → ℂ) (k : ℕ) (p : ℂ × E) : ℂ :=
  poleRemainder (fun s => B (s,p.2)) (fun s => D (s,p.2)) k p.1

theorem jointPoleLeadingNumerator_analyticAt {B D : ℂ × E → ℂ} {p : ℂ × E}
    (hB : AnalyticAt ℂ B p) (hD : AnalyticAt ℂ D p) (k : ℕ) :
    AnalyticAt ℂ (jointPoleLeadingNumerator B D k) p := by
  have hd := parameterDeriv_analyticAt hD
  change AnalyticAt ℂ (fun q => (-1 : ℂ)^k * (k.factorial : ℂ) * B q *
    (parameterDeriv D q)^k) p
  fun_prop

theorem jointPoleRemainder_analyticAt {B D : ℂ × E → ℂ} {p : ℂ × E}
    (hB : AnalyticAt ℂ B p) (hD : AnalyticAt ℂ D p) (k : ℕ) :
    AnalyticAt ℂ (jointPoleRemainder B D k) p := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih =>
    have hl := parameterDeriv_analyticAt (jointPoleLeadingNumerator_analyticAt hB hD k)
    have hr := parameterDeriv_analyticAt ih
    have hd := parameterDeriv_analyticAt hD
    change AnalyticAt ℂ (fun q => parameterDeriv (jointPoleLeadingNumerator B D k) q +
      D q * parameterDeriv (jointPoleRemainder B D k) q -
      (k : ℂ)*parameterDeriv D q*jointPoleRemainder B D k q) p
    fun_prop

/-- The remainder bound is constructed on one joint neighborhood, including
D=0. It is not an additional coefficient-bound hypothesis in applications. -/
theorem jointPoleRemainder_locally_bounded {B D : ℂ × E → ℂ} {p : ℂ × E}
    (hB : AnalyticAt ℂ B p) (hD : AnalyticAt ℂ D p) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ q in 𝓝 p, ‖jointPoleRemainder B D k q‖ ≤ M := by
  let M := ‖jointPoleRemainder B D k p‖+1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  have hc := (jointPoleRemainder_analyticAt hB hD k).continuousAt.norm
  exact (hc.tendsto.eventually (eventually_lt_nhds (show
    ‖jointPoleRemainder B D k p‖ < M by dsimp [M]; linarith))).mono fun _ h => h.le

end
end IsingBulk.First
