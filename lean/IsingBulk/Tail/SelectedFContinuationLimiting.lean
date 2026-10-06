import IsingBulk.Tail.SelectedFContinuation
import IsingBulk.Tail.SelectorCutoffs
import IsingBulk.Tail.RadialDispersionTransfer

/-! The selected contour's compact regular cover is constructed at epsilon=0.
The true lower branch center alone is removed; the upper branch is protected
by its actual fixed inward plateau shift. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

def selectedLimitingShift (f : SelectorFunctions) (τ ρ θ : ℝ) : ℝ :=
  τ*(-2*f.p θ+ρ*f.m θ/2)

def selectedLimitingW (S : ℝ) (f : SelectorFunctions) (τ ρ θ : ℝ) : ℂ :=
  (S:ℂ)-Complex.cosh ((selectedLimitingShift f τ ρ θ:ℝ)+(θ:ℂ)*Complex.I)

theorem selectedLimitingW_components (S : ℝ) (f : SelectorFunctions) (τ ρ θ : ℝ) :
    (selectedLimitingW S f τ ρ θ).re = S-Real.cosh (selectedLimitingShift f τ ρ θ)*Real.cos θ ∧
    (selectedLimitingW S f τ ρ θ).im = -Real.sinh (selectedLimitingShift f τ ρ θ)*Real.sin θ := by
  simp [selectedLimitingW,Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,
    ← Complex.ofReal_cosh,← Complex.ofReal_sinh,← Complex.ofReal_cos,← Complex.ofReal_sin]

theorem selectedLimitingShift_bound (f : SelectorFunctions) {τ ρ θ : ℝ}
    (hτ : 0 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ f.p θ) (hp1 : f.p θ ≤ 1) (hm0 : 0 ≤ f.m θ) (hm1 : f.m θ ≤ 1) :
    |selectedLimitingShift f τ ρ θ| ≤ 2*τ := by
  have hρm0 : 0 ≤ ρ*f.m θ := mul_nonneg hρ0 hm0
  have hρm1 : ρ*f.m θ ≤ 1 := by nlinarith
  have hlow : -2 ≤ -2*f.p θ+ρ*f.m θ/2 := by linarith
  have hhigh : -2*f.p θ+ρ*f.m θ/2 ≤ 2 := by linarith
  rw [abs_le]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlow hτ
    dsimp [selectedLimitingShift]
    linarith
  · simpa only [selectedLimitingShift,mul_comm τ 2] using mul_le_mul_of_nonneg_left hhigh hτ

theorem selectedLimitingW_im_nonneg (S : ℝ) (f : SelectorFunctions) {τ ρ θ : ℝ}
    (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hp : 0 ≤ f.p θ) (hm : 0 ≤ f.m θ)
    (hps : Real.sin θ ≤ 0 → f.p θ=0) (hms : 0 ≤ Real.sin θ → f.m θ=0) :
    0 ≤ (selectedLimitingW S f τ ρ θ).im := by
  rw [(selectedLimitingW_components S f τ ρ θ).2]
  by_cases hs : 0 ≤ Real.sin θ
  · have hv : selectedLimitingShift f τ ρ θ ≤ 0 := by
      simp only [selectedLimitingShift,hms hs,mul_zero,zero_div,add_zero]
      nlinarith
    have hh : Real.sinh (selectedLimitingShift f τ ρ θ) ≤ 0 := by
      simpa using Real.sinh_le_sinh.mpr hv
    exact mul_nonneg (neg_nonneg.mpr hh) hs
  · have hs' := (lt_of_not_ge hs).le
    have hv : 0 ≤ selectedLimitingShift f τ ρ θ := by
      simp only [selectedLimitingShift,hps hs',mul_zero,zero_add]
      positivity
    have hh : 0 ≤ Real.sinh (selectedLimitingShift f τ ρ θ) := by
      simpa using Real.sinh_le_sinh.mpr hv
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hh) hs'

/-- Upper branch reciprocity cannot survive the actual inward p=1 shift.
The only unshifted W=1 possibility is the true lower branch center. -/
theorem selectedLimitingW_ne_one (b : ℝ) (f : SelectorFunctions) {τ ρ θ : ℝ}
    (hτ : 0 < τ) (hb : 0 < Real.sin b)
    (hps : Real.sin θ ≤ 0 → f.p θ=0) (hms : 0 ≤ Real.sin θ → f.m θ=0)
    (hupper : Real.sin θ = Real.sin b → f.p θ=1)
    (hcore : lowerChord b θ ≠ 0) :
    selectedLimitingW (1+Real.cos b) f τ ρ θ ≠ 1 := by
  intro hW
  obtain ⟨hre,him⟩ := selectedLimitingW_components (1+Real.cos b) f τ ρ θ
  rw [hW] at hre him
  norm_num at hre him
  have hv : selectedLimitingShift f τ ρ θ = 0 := by
    rcases him with hv | hs
    · exact hv
    · simp [selectedLimitingShift,hps (by rw [hs]),hms (by rw [hs])]
  rw [hv,Real.cosh_zero,one_mul] at hre
  have hcos : Real.cos θ=Real.cos b := by linarith
  have hsin : (Real.sin θ-Real.sin b)*(Real.sin θ+Real.sin b)=0 := by
    have hθ := Real.sin_sq_add_cos_sq θ
    have hb' := Real.sin_sq_add_cos_sq b
    rw [hcos] at hθ
    nlinarith
  rcases mul_eq_zero.mp hsin with hp | hm
  · have hs : Real.sin θ=Real.sin b := sub_eq_zero.mp hp
    have hzero : selectedLimitingShift f τ ρ θ = -2*τ := by
      simp [selectedLimitingShift,hupper hs,hms (by rw [hs]; exact hb.le)]
      ring
    linarith
  · have hs : Real.sin θ = -Real.sin b := by linarith
    apply hcore
    simp [lowerChord,hcos,hs]

theorem selectedLimitingW_transfer (S : ℝ) (f : SelectorFunctions) (τ ρ θ : ℝ)
    (hv : |selectedLimitingShift f τ ρ θ| ≤ 1) :
    ‖selectedLimitingW S f τ ρ θ-((S-Real.cos θ:ℝ):ℂ)‖ ≤
      2*|selectedLimitingShift f τ ρ θ| := by
  let v := selectedLimitingShift f τ ρ θ
  have htrace := radial_trace_difference_bound v (limitingAngle θ) (limitingAngle_norm θ) hv
  have hy : radialAnglePoint v θ=Complex.exp (v:ℂ)*limitingAngle θ := Complex.exp_add _ _
  have ht : (limitingAngle θ+(limitingAngle θ)⁻¹)/2=(Real.cos θ:ℂ) := by
    rw [limitingAngle_trace]
    ring
  rw [← hy,ht] at htrace
  have he : selectedLimitingW S f τ ρ θ-((S-Real.cos θ:ℝ):ℂ) =
      -((radialAnglePoint v θ+(radialAnglePoint v θ)⁻¹)/2-(Real.cos θ:ℂ)) := by
    simp only [selectedLimitingW,Complex.cosh,radialAnglePoint,← Complex.exp_neg,v]
    push_cast
    ring
  rw [he,norm_neg]
  exact htrace

/-- A compact lower-branch complement has a valid continued-root chart at
all occupancies, with the source upper branch shifted away from its cut. -/
theorem selectedLimitingW_domain (b : ℝ) (f : SelectorFunctions) {τ ρ θ : ℝ}
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos b)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hb : 0 < Real.sin b)
    (hp0 : 0 ≤ f.p θ) (hp1 : f.p θ ≤ 1) (hm0 : 0 ≤ f.m θ) (hm1 : f.m θ ≤ 1)
    (hps : Real.sin θ ≤ 0 → f.p θ=0) (hms : 0 ≤ Real.sin θ → f.m θ=0)
    (hupper : Real.sin θ = Real.sin b → f.p θ=1)
    (hcore : lowerChord b θ ≠ 0) :
    selectedLimitingW (1+Real.cos b) f τ ρ θ ∈ continuedRootDomain := by
  have hshift := selectedLimitingShift_bound f hτ.le hρ0 hρ1 hp0 hp1 hm0 hm1
  have hmove := selectedLimitingW_transfer (1+Real.cos b) f τ ρ θ (hshift.trans hτsmall)
  have hre : -1 < (selectedLimitingW (1+Real.cos b) f τ ρ θ).re := by
    have hh := Complex.abs_re_le_norm
      (selectedLimitingW (1+Real.cos b) f τ ρ θ-((1+Real.cos b-Real.cos θ:ℝ):ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    have hl := (abs_le.mp (hh.trans hmove)).1
    linarith [Real.cos_le_one θ]
  have him := selectedLimitingW_im_nonneg (1+Real.cos b) f hτ.le hρ0 hp0 hm0 hps hms
  by_cases hi : 0 < (selectedLimitingW (1+Real.cos b) f τ ρ θ).im
  · exact Or.inl (Or.inl hi)
  · have hi0 : (selectedLimitingW (1+Real.cos b) f τ ρ θ).im=0 := by linarith
    have hrne : (selectedLimitingW (1+Real.cos b) f τ ρ θ).re ≠ 1 := by
      intro he
      apply selectedLimitingW_ne_one b f hτ hb hps hms hupper hcore
      exact Complex.ext he hi0
    by_cases hl : 1 < (selectedLimitingW (1+Real.cos b) f τ ρ θ).re
    · exact Or.inl (Or.inr hl)
    · exact Or.inr (abs_lt.mpr ⟨hre,lt_of_le_of_ne (le_of_not_gt hl) hrne⟩)

end
end IsingBulk.Tail
