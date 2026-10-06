import IsingBulk.First.PeriodicAngularChart
import IsingBulk.First.SmoothCutoffConstruction
import Mathlib.Analysis.Real.Pi.Bounds

/-! Globally smooth, periodic y-only weights with the exact fixed real
shape/mean product in their local chart. No x or source-radius variable occurs. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set Metric
open scoped Topology ContDiff BigOperators
attribute [local fun_prop] angularGate_contDiff

def angularChartVector {N : ℕ} (alpha : ℝ) (theta : Fin N → ℝ) : Fin N → ℝ :=
  fun j => periodicAngle (theta j+alpha)

def angularChartGate {N : ℕ} (alpha : ℝ) (theta : Fin N → ℝ) : ℝ :=
  ∏ j, angularGate (theta j+alpha)

def fixedYChartWeight {n : ℕ} (alpha : ℝ) (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ)
    (theta : Fin (n+1) → ℝ) : ℝ :=
  angularChartGate alpha theta *
    chi (fun j => shapeCoordinates (angularChartVector alpha theta) j.castSucc) *
    eta (meanCoordinate (angularChartVector alpha theta))

theorem angularChartGate_contDiff (N : ℕ) (alpha : ℝ) : ContDiff ℝ ∞ (@angularChartGate N alpha) := by
  unfold angularChartGate
  fun_prop

theorem angularChartGate_tsupport {N : ℕ} (alpha : ℝ) {theta : Fin N → ℝ}
    (ht : theta ∈ tsupport (angularChartGate alpha)) (j : Fin N) :
    1/2 ≤ Real.cos (theta j+alpha) := by
  have hsub : Function.support (angularChartGate alpha) ⊆
      {t : Fin N → ℝ | 1/2 ≤ Real.cos (t j+alpha)} := by
    intro t ht
    have hn : angularGate (t j+alpha) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp ht j (Finset.mem_univ j)
    exact angularGate_tsupport (subset_closure hn)
  exact closure_minimal hsub (isClosed_le continuous_const (by fun_prop)) ht

theorem fixedYChartWeight_contDiff {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ chi) (he : ContDiff ℝ ∞ eta) :
    ContDiff ℝ ∞ (fixedYChartWeight alpha chi eta) := by
  rw [contDiff_iff_contDiffAt]
  intro theta
  by_cases ht : theta ∈ tsupport (angularChartGate alpha)
  · have hu (j : Fin (n+1)) : ContDiffAt ℝ ∞
        (fun t : Fin (n+1) → ℝ => periodicAngle (t j+alpha)) theta := by
      have hcos : 0 < Real.cos (theta j+alpha) := by linarith [angularChartGate_tsupport alpha ht j]
      exact ContDiffAt.comp (f := fun t : Fin (n+1) → ℝ => t j+alpha)
        (g := periodicAngle) theta (periodicAngle_contDiffAt hcos) (by fun_prop)
    have hm : ContDiffAt ℝ ∞ (fun t : Fin (n+1) → ℝ => meanCoordinate (angularChartVector alpha t)) theta := by
      unfold meanCoordinate angularChartVector
      fun_prop
    have hs : ContDiffAt ℝ ∞ (fun t : Fin (n+1) → ℝ =>
        fun j : Fin n => shapeCoordinates (angularChartVector alpha t) j.castSucc) theta := by
      unfold shapeCoordinates angularChartVector
      fun_prop
    exact ((angularChartGate_contDiff (n+1) alpha).contDiffAt.mul (hc.contDiffAt.comp theta hs)).mul
      (he.contDiffAt.comp theta hm)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp ht
    have hf : fixedYChartWeight alpha chi eta =ᶠ[𝓝 theta] (fun _ => (0:ℝ)) := by
      filter_upwards [hz] with t ht
      simp [fixedYChartWeight,ht]
    exact contDiffAt_const.congr_of_eventuallyEq hf

theorem angularChartVector_update_period {N : ℕ} (alpha : ℝ) (theta : Fin N → ℝ) (j : Fin N) :
    angularChartVector alpha (Function.update theta j (theta j+2*Real.pi)) = angularChartVector alpha theta := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [angularChartVector, Function.update_self]
    rw [show theta j+2*Real.pi+alpha = (theta j+alpha)+2*Real.pi by ring,
      periodicAngle_periodic]
  · simp [angularChartVector, Function.update_of_ne hi]

theorem angularChartGate_update_period {N : ℕ} (alpha : ℝ) (theta : Fin N → ℝ) (j : Fin N) :
    angularChartGate alpha (Function.update theta j (theta j+2*Real.pi)) = angularChartGate alpha theta := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    simp only [Function.update_self]
    rw [show theta j+2*Real.pi+alpha = (theta j+alpha)+2*Real.pi by ring,
      angularGate_periodic]
  · simp [Function.update_of_ne hi]

theorem fixedYChartWeight_update_period {n : ℕ} (alpha : ℝ)
    (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ) (theta : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    fixedYChartWeight alpha chi eta (Function.update theta j (theta j+2*Real.pi)) =
      fixedYChartWeight alpha chi eta theta := by
  simp only [fixedYChartWeight, angularChartVector_update_period, angularChartGate_update_period]

/-- The local product is literal: the real shape cutoff remains fixed when
the mean segment is moved, rather than being analytically continued. -/
theorem fixedYChartWeight_meanShape {n : ℕ} (alpha : ℝ)
    (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ) (v : ℝ) (t : Fin n → ℝ)
    (hu : ∀ j : Fin (n+1), |meanShapeChart v t j| ≤ 1/2) :
    fixedYChartWeight alpha chi eta (fun j => meanShapeChart v t j-alpha) = chi t*eta v := by
  have hN : (n+1:ℝ) ≠ 0 := by positivity
  have hv : angularChartVector alpha (fun j => meanShapeChart v t j-alpha) = meanShapeChart v t := by
    funext j
    simp only [angularChartVector, sub_add_cancel]
    apply periodicAngle_eq <;> have hh := abs_le.mp (hu j) <;> linarith [Real.pi_gt_three]
  have hg : angularChartGate alpha (fun j => meanShapeChart v t j-alpha) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    simp only [sub_add_cancel]
    apply angularGate_eq_one
    have hh := abs_le.mp (hu j)
    have hc := Real.one_sub_sq_div_two_le_cos (x := meanShapeChart v t j)
    nlinarith
  simp only [fixedYChartWeight, hg, hv, shapeCoordinates_meanShapeChart hN,
    shapeExtend_castSucc, meanCoordinate_meanShapeChart hN, one_mul]

end
end IsingBulk.First
