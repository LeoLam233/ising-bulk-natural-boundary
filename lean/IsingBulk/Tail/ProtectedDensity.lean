import IsingBulk.Tail.ProtectedSourceRoots
import IsingBulk.Tail.SelectedFContinuationIntegral

/-! Literal named-current continuations and fixed-weight angular integrals.
The support restriction is retained, and no cutoff is analytically extended. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

def continuedNamedCurrentDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*continuedPulledDensity f r τ lam s θ

def namedCurrentAngularWeight (N : ℕ) (f : SelectorFunctions) (τ lam : ℝ)
    (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*(N.factorial:ℂ)⁻¹ *
    (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ))*(angularJacobian f τ lam θ).det

def continuedNamedCurrentIntegral (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, continuedNamedCurrentDensity f r τ lam s q θ

def actualNamedCurrentIntegral (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, namedCurrentDensity f r τ lam s q θ

def continuedCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, continuedNamedCurrentIntegral N f r τ lam q s

def actualCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, actualNamedCurrentIntegral N f r τ lam q s

def differentiatedCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (j : ℕ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, ∫ θ in angleBox N,
    iteratedDeriv j (fun z => namedCurrentDensity f r τ lam z q θ) s

theorem continuedNamedCurrentDensity_weighted {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) :
    continuedNamedCurrentDensity f r τ lam s q θ =
      namedCurrentAngularWeight N f τ lam q θ *
        continuedContourDensity N (s,deformedPoint f r τ lam θ) := by
  unfold continuedNamedCurrentDensity namedCurrentAngularWeight continuedPulledDensity continuedContourDensity
  ring

theorem continuedPulledDensity_analyticAt {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : 1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : 1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticAt ℂ (fun z => continuedPulledDensity f r τ lam z θ) s := by
  have ha₀ : AnalyticAt ℂ (continuedContourDensity N) (s,deformedPoint f r τ lam θ) :=
    continuedContourDensity_analyticAt (p := (s,deformedPoint f r τ lam θ)) hs
      (deformedPoint_nonzero f hr τ lam θ) hW hY hZ
  have hmap : AnalyticAt ℂ (fun z : ℂ => (z,deformedPoint f r τ lam θ)) s :=
    analyticAt_id.prod analyticAt_const
  have ha := ha₀.comp (f := fun z : ℂ => (z,deformedPoint f r τ lam θ)) hmap
  have he : (fun z => continuedPulledDensity f r τ lam z θ) =
      (fun z => ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det)*continuedContourDensity N (z,deformedPoint f r τ lam θ)) := by
    funext z
    unfold continuedPulledDensity continuedContourDensity
    ring
  rw [he]
  exact analyticAt_const.mul ha

theorem continuedNamedCurrentDensity_analyticAt {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
    {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : 1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : 1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticAt ℂ (fun z => continuedNamedCurrentDensity f r τ lam z q θ) s :=
  analyticAt_const.mul (continuedPulledDensity_analyticAt f hr τ lam θ hs hW hY hZ)

theorem namedCurrentAngularWeight_continuous (N : ℕ) (f : SelectorFunctions) (τ lam : ℝ)
    (q : Fin N) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a) :
    Continuous (namedCurrentAngularWeight N f τ lam q) := by
  have hpd : ContDiff ℝ ∞ (deriv f.p) := by apply ContDiff.deriv'; simpa using hp
  have hmd : ContDiff ℝ ∞ (deriv f.m) := by apply ContDiff.deriv'; simpa using hm
  have had : ContDiff ℝ ∞ (deriv f.a) := by apply ContDiff.deriv'; simpa using ha
  have hp' := hpd.continuous
  have hm' := hmd.continuous
  have ha' := had.continuous
  have hp0 := hp.continuous
  have hm0 := hm.continuous
  have ha0 := ha.continuous
  have hJ : Continuous (fun θ : Fin N → ℝ => angularJacobian f τ lam θ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold angularJacobian retractionJacobian occupancy
    by_cases hij : i=j <;> simp only [hij,ite_true,ite_false] <;> fun_prop
  have hweight : Continuous (fun θ : Fin N → ℝ => namedSelectorDerivative f q θ) := by
    unfold namedSelectorDerivative
    fun_prop
  have hdet := hJ.matrix_det
  unfold namedCurrentAngularWeight
  fun_prop

theorem continuedNamedCurrentIntegral_eq_supported (N : ℕ) (f : SelectorFunctions)
    (r τ lam : ℝ) (q : Fin N) (s : ℂ) :
    continuedNamedCurrentIntegral N f r τ lam q s =
      ∫ θ in angleBox N ∩ tsupport (namedSelectorDerivative f q),
        namedCurrentAngularWeight N f τ lam q θ *
          continuedContourDensity N (s,deformedPoint f r τ lam θ) := by
  unfold continuedNamedCurrentIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (namedSelectorDerivative f q))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _
    exact continuedNamedCurrentDensity_weighted f r τ lam s q θ
  · intro θ hθ
    have hh : θ ∉ tsupport (namedSelectorDerivative f q) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp [continuedNamedCurrentDensity,hz]

theorem continuedNamedCurrentIntegral_analyticOn_of_gaps (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticOnNhd ℂ (continuedNamedCurrentIntegral N f r τ lam q) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (namedSelectorDerivative f q)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (continuedContourDensity N)
    (deformedPoint f r τ lam) (deformedPoint_continuous f r τ lam hp.continuous hm.continuous)
    (namedCurrentAngularWeight N f τ lam q) (namedCurrentAngularWeight_continuous N f τ lam q hp hm ha)
    (fun t ht θ hθ => continuedContourDensity_analyticAt (hs t ht)
      (deformedPoint_nonzero f hr τ lam θ) (hW t ht θ hθ) (hY θ hθ) (hZ t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (continuedNamedCurrentIntegral_eq_supported N f r τ lam q t).symm)

end
end IsingBulk.Tail
