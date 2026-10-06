import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! A globally periodic real angular chart with a smooth gate killing the
principal-log seam. It will carry fixed real shape/mean cutoffs only. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set Metric
open scoped Topology ContDiff

def periodicAngle (u : ℝ) : ℝ := (Complex.log (Complex.exp ((u:ℂ)*I))).im

theorem periodicAngle_eq {u : ℝ} (hl : -Real.pi < u) (hu : u ≤ Real.pi) :
    periodicAngle u = u := by
  unfold periodicAngle
  rw [Complex.log_exp]
  · simp
  · simpa using hl
  · simpa using hu

theorem periodicAngle_periodic : Function.Periodic periodicAngle (2*Real.pi) := by
  intro u
  unfold periodicAngle
  have he : (((u+2*Real.pi:ℝ):ℂ)*I) = (u:ℂ)*I+2*Real.pi*I := by push_cast; ring
  rw [he, Complex.exp_periodic]

theorem periodicAngle_contDiffAt {u : ℝ} (hu : 0 < Real.cos u) :
    ContDiffAt ℝ ∞ periodicAngle u := by
  have hs : exp ((u:ℂ)*I) ∈ Complex.slitPlane := Or.inl (by simpa using hu)
  have hl : ContDiffAt ℝ ∞ Complex.log (exp ((u:ℂ)*I)) :=
    (Complex.contDiffAt_log hs).restrict_scalars ℝ
  have hi : ContDiffAt ℝ ∞ (fun v : ℝ => (v:ℂ)*I) u :=
    Complex.ofRealCLM.contDiff.contDiffAt.mul contDiffAt_const
  have he : ContDiffAt ℝ ∞ (fun v : ℝ => exp ((v:ℂ)*I)) u := hi.cexp
  exact Complex.imCLM.contDiff.contDiffAt.comp u (hl.comp u he)

def angularGateBump : ContDiffBump (1:ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def angularGate (u : ℝ) : ℝ := angularGateBump (Real.cos u)

theorem angularGate_contDiff : ContDiff ℝ ∞ angularGate :=
  angularGateBump.contDiff.comp Real.contDiff_cos

theorem angularGate_nonneg (u : ℝ) : 0 ≤ angularGate u := angularGateBump.nonneg

theorem angularGate_le_one (u : ℝ) : angularGate u ≤ 1 := angularGateBump.le_one

theorem angularGate_eq_one {u : ℝ} (hu : 3/4 ≤ Real.cos u) : angularGate u = 1 := by
  apply angularGateBump.one_of_mem_closedBall
  change dist (Real.cos u) 1 ≤ 1/4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [Real.cos_le_one u]

theorem angularGate_periodic : Function.Periodic angularGate (2*Real.pi) := by
  intro u
  simp only [angularGate, Real.cos_add_two_pi]

theorem angularGate_tsupport {u : ℝ} (hu : u ∈ tsupport angularGate) :
    1/2 ≤ Real.cos u := by
  have hsub : Function.support angularGate ⊆ {v : ℝ | 1/2 ≤ Real.cos v} := by
    intro v hv
    have hb : Real.cos v ∈ Function.support angularGateBump := hv
    rw [angularGateBump.support_eq] at hb
    change dist (Real.cos v) 1 < 1/2 at hb
    rw [Real.dist_eq, abs_lt] at hb
    change 1/2 ≤ Real.cos v
    linarith [hb.1]
  exact closure_minimal hsub (isClosed_le continuous_const Real.continuous_cos) hu

theorem angularGate_mul_contDiff (f : ℝ → ℝ)
    (hf : ∀ u, 0 < Real.cos u → ContDiffAt ℝ ∞ f u) :
    ContDiff ℝ ∞ (fun u => angularGate u*f u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport angularGate
  · exact angularGate_contDiff.contDiffAt.mul (hf u (by linarith [angularGate_tsupport hu]))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hu
    have he : (fun u => angularGate u*f u) =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
      filter_upwards [hz] with v hv
      simp [hv]
    exact contDiffAt_const.congr_of_eventuallyEq he

end
end IsingBulk.First
