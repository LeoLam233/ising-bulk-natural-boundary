import IsingBulk.Preferred22.Coordinates

/-!
# HT22: the unshifted regular inverse and its continued square root

F001 uses v = w + φ, whereas Preferred22's moving coordinate is
q = v − preferredMovingBranch(t).  The equality below exposes this change;
no estimate for fixed q is mislabeled as an estimate for fixed v.
-/

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Set Filter IsingBulk.Preferred22

def physicalPhase (t w : ℂ) : ℂ :=
  preferredArccos (temperatureTrace t - Complex.cos w)

def sumCoordinate (t w : ℂ) : ℂ := w + physicalPhase t w

def regularInverse (t v : ℂ) : ℂ := complexRightInverse (temperatureTrace t) v

def regularPhase (t v : ℂ) : ℂ := v - regularInverse t v

/-- This is a continued root defined by the physical inverse, not `sqrt D`. -/
def continuedRoot (t v : ℂ) : ℂ :=
  Complex.sin (regularPhase t v) - Complex.sin (regularInverse t v)

theorem regularInverse_moving_adapter (t v : ℂ) :
    regularInverse t v = preferredMovingInverse t (v - preferredMovingBranch t) := by
  simp only [regularInverse, preferredMovingInverse, traceMovingInverse,
    preferredMovingBranch, sub_add_cancel]

theorem regularInverse_dispersion (t v : ℂ) (hc : Complex.cos (v / 2) ≠ 0) :
    Complex.cos (regularInverse t v) + Complex.cos (regularPhase t v) =
      temperatureTrace t :=
  complexRightInverse_dispersion (temperatureTrace t) v hc

theorem physicalPhase_root (t w : ℂ)
    (hW : 0 < (temperatureTrace t - Complex.cos w).im) :
    Complex.exp (-Complex.I * physicalPhase t w) =
      physicalRoot (temperatureTrace t - Complex.cos w) :=
  preferredArccos_physical_upper _ hW

theorem global_one_sided_inverse (t w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (hS : 0 < (temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re < 2 * Real.cos δ)
    (hlo : -Real.pi - δ ≤ w.re) (hhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace t - Complex.cos w).im) :
    regularInverse t (sumCoordinate t w) = w := by
  rw [regularInverse_moving_adapter]
  simpa only [sumCoordinate, physicalPhase, add_comm w] using
    preferred_global_one_sided_inverse t w δ hδ hδπ hS hSδ hlo hhi hW

theorem global_one_sided_phase (t w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (hS : 0 < (temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re < 2 * Real.cos δ)
    (hlo : -Real.pi - δ ≤ w.re) (hhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace t - Complex.cos w).im) :
    regularPhase t (sumCoordinate t w) = physicalPhase t w := by
  rw [regularPhase, global_one_sided_inverse t w δ hδ hδπ hS hSδ hlo hhi hW]
  simp [sumCoordinate]

theorem regularInverse_analyticAt_of_strip (t w φ : ℂ)
    (hdisp : Complex.cos w + Complex.cos φ = temperatureTrace t)
    (hc : Complex.cos ((w + φ) / 2) ≠ 0)
    (hl : 0 < ((φ - w) / 2).re) (hu : ((φ - w) / 2).re < Real.pi) :
    AnalyticAt ℂ (regularInverse t) (w + φ) := by
  have hraw := complexRightInverse_analyticAt_of_strip (temperatureTrace t) w φ
    hdisp hc hl hu
  exact AnalyticAt.comp (f := fun v : ℂ => (temperatureTrace t, v))
    (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw
    (analyticAt_const.prod analyticAt_id)

/-- Joint analyticity is for the unshifted v coordinate, not for a moving q. -/
theorem regularInverse_joint_analytic_of_strip (t w φ : ℂ) (ht : t ≠ 0)
    (hdisp : Complex.cos w + Complex.cos φ = temperatureTrace t)
    (hc : Complex.cos ((w + φ) / 2) ≠ 0)
    (hl : 0 < ((φ - w) / 2).re) (hu : ((φ - w) / 2).re < Real.pi) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t, w + φ) := by
  have hraw := complexRightInverse_analyticAt_of_strip (temperatureTrace t) w φ
    hdisp hc hl hu
  have htrace : AnalyticAt ℂ (fun z : ℂ × ℂ => temperatureTrace z.1) (t, w + φ) :=
    analyticAt_fst.add (analyticAt_fst.inv ht)
  exact AnalyticAt.comp (f := fun z : ℂ × ℂ => (temperatureTrace z.1, z.2))
    (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw
    (htrace.prod analyticAt_snd)

/-- Pointwise analyticity of F001's unshifted inverse on the full physical
one-sided contour. Uniform tubes and all-N estimates are separate duties. -/
theorem global_one_sided_analytic (t w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (hS : 0 < (temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re < 2 * Real.cos δ)
    (hlo : -Real.pi - δ ≤ w.re) (hhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace t - Complex.cos w).im) :
    AnalyticAt ℂ (regularInverse t) (sumCoordinate t w) := by
  obtain ⟨hl, hu⟩ := preferred_half_difference_strip (temperatureTrace t) w δ
    hδ hδπ hS hSδ hlo hhi hW
  have hdisp : Complex.cos w + Complex.cos (physicalPhase t w) = temperatureTrace t := by
    rw [physicalPhase, cos_preferredArccos]
    ring
  have hc : Complex.cos ((w + physicalPhase t w) / 2) ≠ 0 := by
    intro hz
    have hh := Complex.cos_add_cos w (physicalPhase t w)
    rw [hz, mul_zero, zero_mul, hdisp] at hh
    rw [hh, Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  exact regularInverse_analyticAt_of_strip t w (physicalPhase t w) hdisp hc hl hu

theorem global_one_sided_joint_analytic (t w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (hS : 0 < (temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re < 2 * Real.cos δ)
    (hlo : -Real.pi - δ ≤ w.re) (hhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace t - Complex.cos w).im) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2)
      (t, sumCoordinate t w) := by
  have ht : t ≠ 0 := by
    intro hz
    simp [hz, temperatureTrace] at hS
  obtain ⟨hl, hu⟩ := preferred_half_difference_strip (temperatureTrace t) w δ
    hδ hδπ hS hSδ hlo hhi hW
  have hdisp : Complex.cos w + Complex.cos (physicalPhase t w) = temperatureTrace t := by
    rw [physicalPhase, cos_preferredArccos]
    ring
  have hc : Complex.cos ((w + physicalPhase t w) / 2) ≠ 0 := by
    intro hz
    have hh := Complex.cos_add_cos w (physicalPhase t w)
    rw [hz, mul_zero, zero_mul, hdisp] at hh
    rw [hh, Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  exact regularInverse_joint_analytic_of_strip t w (physicalPhase t w) ht hdisp hc hl hu

/-- Implicit differentiation fixes the sign of the continued root exactly. -/
theorem regularInverse_derivative_identity (t v : ℂ)
    (hc : Complex.cos (v / 2) ≠ 0)
    (hU : AnalyticAt ℂ (regularInverse t) v) :
    continuedRoot t v * deriv (regularInverse t) v = Complex.sin (regularPhase t v) := by
  have hd := hU.differentiableAt.hasDerivAt.ccos.add
    (((hasDerivAt_id v).sub hU.differentiableAt.hasDerivAt).ccos)
  have hnear : ∀ᶠ u in 𝓝 v, Complex.cos (u / 2) ≠ 0 :=
    (by fun_prop : ContinuousAt (fun u : ℂ => Complex.cos (u / 2)) v).eventually_ne hc
  have heq : (fun u => Complex.cos (regularInverse t u) +
      Complex.cos (u - regularInverse t u)) =ᶠ[𝓝 v] (fun _ => temperatureTrace t) := by
    filter_upwards [hnear] with u hu
    exact regularInverse_dispersion t u hu
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const v (temperatureTrace t))
  simp only [Pi.sub_apply, id_eq] at he
  dsimp only [continuedRoot, regularPhase]
  linear_combination he

theorem continuedRoot_ne_zero (t v : ℂ)
    (hc : Complex.cos (v / 2) ≠ 0)
    (hU : AnalyticAt ℂ (regularInverse t) v)
    (hs : Complex.sin (regularPhase t v) ≠ 0) : continuedRoot t v ≠ 0 := by
  intro hz
  have he := regularInverse_derivative_identity t v hc hU
  rw [hz, zero_mul] at he
  exact hs he.symm

theorem regularInverse_derivative (t v : ℂ)
    (hc : Complex.cos (v / 2) ≠ 0)
    (hU : AnalyticAt ℂ (regularInverse t) v)
    (hs : Complex.sin (regularPhase t v) ≠ 0) :
    deriv (regularInverse t) v =
      Complex.sin (regularPhase t v) / continuedRoot t v := by
  apply (eq_div_iff (continuedRoot_ne_zero t v hc hU hs)).2
  simpa only [mul_comm] using regularInverse_derivative_identity t v hc hU

/-- Genuine fixed-v parameter differentiation of the dispersion identity. -/
theorem regularInverse_parameter_identity (t v : ℂ) (ht : t ≠ 0)
    (hc : Complex.cos (v / 2) ≠ 0)
    (hU : AnalyticAt ℂ (fun s => regularInverse s v) t) :
    continuedRoot t v * deriv (fun s => regularInverse s v) t =
      deriv temperatureTrace t := by
  have htrace : AnalyticAt ℂ temperatureTrace t := analyticAt_id.add (analyticAt_id.inv ht)
  have hd := hU.differentiableAt.hasDerivAt.ccos.add
    (((hasDerivAt_const t v).sub hU.differentiableAt.hasDerivAt).ccos)
  have heq : (fun s => Complex.cos (regularInverse s v) +
      Complex.cos (v - regularInverse s v)) = temperatureTrace := by
    funext s
    exact regularInverse_dispersion s v hc
  have heg : (fun s => Complex.cos (regularInverse s v) +
      Complex.cos (v - regularInverse s v)) =ᶠ[𝓝 t] temperatureTrace :=
    Filter.Eventually.of_forall (fun s => congrFun heq s)
  have he := (hd.congr_of_eventuallyEq heg.symm).unique htrace.differentiableAt.hasDerivAt
  dsimp only [Pi.sub_apply] at he
  dsimp only [continuedRoot, regularPhase]
  linear_combination he

theorem regularInverse_parameter_derivative (t v : ℂ) (ht : t ≠ 0)
    (hc : Complex.cos (v / 2) ≠ 0)
    (hUv : AnalyticAt ℂ (regularInverse t) v)
    (hUt : AnalyticAt ℂ (fun s => regularInverse s v) t)
    (hs : Complex.sin (regularPhase t v) ≠ 0) :
    deriv (fun s => regularInverse s v) t =
      deriv temperatureTrace t / continuedRoot t v := by
  apply (eq_div_iff (continuedRoot_ne_zero t v hc hUv hs)).2
  simpa only [mul_comm] using regularInverse_parameter_identity t v ht hc hUt

end
end IsingBulk.HT22.Geometry
