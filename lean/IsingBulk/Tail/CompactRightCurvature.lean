import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual limiting compact-right phase, before the coupled-contour
perturbation. No curvature premise is used to obtain these source formulas. -/
namespace IsingBulk.Tail
noncomputable section
open scoped Topology

def compactRightPhase (S θ : ℝ) : ℝ := Real.arccos (S-Real.cos θ)
def compactRightSlope (S θ : ℝ) : ℝ :=
  -Real.sin θ/Real.sqrt (1-(S-Real.cos θ)^2)

theorem compactRightPhase_hasDerivAt (S θ : ℝ) (h : |S-Real.cos θ| < 1) :
    HasDerivAt (compactRightPhase S) (compactRightSlope S θ) θ := by
  have hh := abs_lt.mp h
  have hw : HasDerivAt (fun t : ℝ => S-Real.cos t) (Real.sin θ) θ := by
    simpa using (Real.hasDerivAt_cos θ).const_sub S
  have ha := (Real.hasDerivAt_arccos (by linarith : S-Real.cos θ ≠ -1)
    (by linarith : S-Real.cos θ ≠ 1)).comp θ hw
  convert! ha using 1
  simp [compactRightSlope,div_eq_mul_inv,mul_comm]

theorem compact_curvature_algebra {S c v r : ℝ} (hr : r ≠ 0)
    (hunit : v^2+c^2=1) (hsqrt : r^2=1-(S-c)^2) :
    (-c*r-(-v)*(-(S-c)*v/r))/r^2 = -S*(1-c*(S-c))/r^3 := by
  calc
    _ = (-c*r^2-(S-c)*v^2)/r^3 := by field_simp
    _ = _ := by
      congr 1
      rw [hsqrt,show v^2=1-c^2 by linarith]
      ring

theorem compactRightPhase_second_hasDerivAt (S θ : ℝ) (h : |S-Real.cos θ| < 1) :
    HasDerivAt (deriv (compactRightPhase S))
      (-S*(1-Real.cos θ*(S-Real.cos θ))/
        (Real.sqrt (1-(S-Real.cos θ)^2))^3) θ := by
  have hh := abs_lt.mp h
  have hq : 0 < 1-(S-Real.cos θ)^2 := by nlinarith
  have hr : Real.sqrt (1-(S-Real.cos θ)^2) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hw : HasDerivAt (fun t : ℝ => S-Real.cos t) (Real.sin θ) θ := by
    simpa using (Real.hasDerivAt_cos θ).const_sub S
  have hq' : HasDerivAt (fun t : ℝ => 1-(S-Real.cos t)^2)
      (-2*(S-Real.cos θ)*Real.sin θ) θ := by
    convert (hw.pow 2).const_sub 1 using 1; ring
  have hs := (Real.hasDerivAt_sqrt hq.ne').comp θ hq'
  have hs' : HasDerivAt (fun t : ℝ => Real.sqrt (1-(S-Real.cos t)^2))
      (-(S-Real.cos θ)*Real.sin θ/Real.sqrt (1-(S-Real.cos θ)^2)) θ := by
    convert! hs using 1; field_simp
  have hquot := (Real.hasDerivAt_sin θ).neg.div hs' hr
  simp only [Pi.neg_apply] at hquot
  have halg := compact_curvature_algebra hr (Real.sin_sq_add_cos_sq θ) (Real.sq_sqrt hq.le)
  rw [halg] at hquot
  have hc : Continuous (fun t : ℝ => |S-Real.cos t|) := by fun_prop
  have hevent : ∀ᶠ t in 𝓝 θ, |S-Real.cos t| < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds h)
  have heq : deriv (compactRightPhase S) =ᶠ[𝓝 θ] compactRightSlope S := by
    filter_upwards [hevent] with t ht
    exact (compactRightPhase_hasDerivAt S t ht).deriv
  exact hquot.congr_of_eventuallyEq heq

theorem compactRightPhase_second_deriv (S θ : ℝ) (h : |S-Real.cos θ| < 1) :
    deriv (deriv (compactRightPhase S)) θ =
      -S*(1-Real.cos θ*(S-Real.cos θ))/(Real.sqrt (1-(S-Real.cos θ)^2))^3 :=
  (compactRightPhase_second_hasDerivAt S θ h).deriv

/-- An explicit uniform limiting curvature constant on a compact-right
margin. The later coupled Hessian perturbation remains a separate step. -/
theorem compactRightPhase_uniform_curvature {S δ : ℝ} (hS : 0 < S) (hδ : 0 < δ)
    (θ : ℝ) (hmargin : |S-Real.cos θ| ≤ 1-δ) :
    deriv (deriv (compactRightPhase S)) θ ≤ -S*δ := by
  have hw : |S-Real.cos θ| < 1 := by linarith
  have hww := abs_lt.mp hw
  have hq : 0 < 1-(S-Real.cos θ)^2 := by nlinarith
  have hr : 0 < Real.sqrt (1-(S-Real.cos θ)^2) := Real.sqrt_pos.mpr hq
  have hr1 : Real.sqrt (1-(S-Real.cos θ)^2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have hprod : Real.cos θ*(S-Real.cos θ) ≤ |S-Real.cos θ| := by
    calc
      _ ≤ |Real.cos θ*(S-Real.cos θ)| := le_abs_self _
      _ = |Real.cos θ| * |S-Real.cos θ| := abs_mul _ _
      _ ≤ |S-Real.cos θ| := mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
  have hn : δ ≤ 1-Real.cos θ*(S-Real.cos θ) := by linarith
  rw [compactRightPhase_second_deriv S θ hw]
  apply (div_le_iff₀ (pow_pos hr 3)).mpr
  have hp := pow_le_one₀ hr.le hr1 (n := 3)
  have h₁ := mul_le_mul_of_nonneg_left hn hS.le
  have h₂ := mul_le_mul_of_nonneg_left hp (mul_pos hS hδ).le
  nlinarith

/-- The limiting selected-pair Jacobian has a uniform divided-difference
margin on every actual compact-right interval. -/
theorem compactRightPhase_slope_gap {S δ x y : ℝ} (hS : 0 < S) (hδ : 0 < δ)
    (hxy : x ≤ y) (hmargin : ∀ θ ∈ Set.Icc x y, |S-Real.cos θ| ≤ 1-δ) :
    S*δ*(y-x) ≤ deriv (compactRightPhase S) x-deriv (compactRightPhase S) y := by
  have hd (θ : ℝ) (hθ : θ ∈ Set.Icc x y) :
      DifferentiableAt ℝ (deriv (compactRightPhase S)) θ :=
    (compactRightPhase_second_hasDerivAt S θ (by have := hmargin θ hθ; linarith)).differentiableAt
  have hc : ContinuousOn (deriv (compactRightPhase S)) (Set.Icc x y) :=
    fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (deriv (compactRightPhase S)) (interior (Set.Icc x y)) :=
    fun θ hθ => (hd θ (interior_subset hθ)).differentiableWithinAt
  have hbound : ∀ θ ∈ interior (Set.Icc x y),
      deriv (deriv (compactRightPhase S)) θ ≤ -S*δ :=
    fun θ hθ => compactRightPhase_uniform_curvature hS hδ θ (hmargin θ (interior_subset hθ))
  have h := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le hc hdiff hbound
    x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
  linarith

end
end IsingBulk.Tail
