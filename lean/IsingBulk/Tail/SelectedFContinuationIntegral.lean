import IsingBulk.Tail.SelectedFDisk
import IsingBulk.First.CompactIntegralHolomorphic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Instances.Matrix

/-! Holomorphy of the complete selected-F integral with fixed angular
weights. Pointwise assignments used in later absolute estimates do not enter
this analytic integral. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

 def continuedContourDensity (N : ℕ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, p.2 i)*canceledReducedDensity (fun i => selectedContinuedRoot p.1 (p.2 i)) p.2

 theorem continuedContourDensity_analyticAt {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (hs : p.1 ≠ 0) (hy : ∀ i, p.2 i ≠ 0)
    (hW : ∀ i, sourceW p.1 (p.2 i) ∈ continuedRootDomain)
    (hY : 1-coordinateProduct p.2 ≠ 0)
    (hZ : 1-coordinateProduct (fun i => selectedContinuedRoot p.1 (p.2 i)) ≠ 0) :
    AnalyticAt ℂ (continuedContourDensity N) p := by
  let y : (ℂ × (Fin N → ℂ)) → Fin N → ℂ := fun q => q.2
  let z : (ℂ × (Fin N → ℂ)) → Fin N → ℂ := fun q i => selectedContinuedRoot q.1 (q.2 i)
  have dy (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => y q i) p :=
    ((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp analyticAt_snd
  have dz (i : Fin N) : AnalyticAt ℂ (fun q => z q i) p := by
    have dW : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => sourceW q.1 (q.2 i)) p :=
      (analyticAt_fst.add (analyticAt_fst.inv hs)).sub
        (((dy i).add ((dy i).inv (hy i))).div analyticAt_const (by norm_num))
    exact (continuedRoot_analyticAt (hW i)).comp (f := fun q : ℂ × (Fin N → ℂ) => sourceW q.1 (q.2 i)) dW
  have hz0 (i : Fin N) : z p i ≠ 0 := continuedRoot_nonzero _
  have hpair (i j : Fin N) : 1-z p i*z p j ≠ 0 := continuedRoot_pair_gap (hW i) (hW j)
  have dY : AnalyticAt ℂ (fun q => coordinateProduct (y q)) p :=
    Finset.analyticAt_fun_prod _ (fun i _ => dy i)
  have dZ : AnalyticAt ℂ (fun q => coordinateProduct (z q)) p :=
    Finset.analyticAt_fun_prod _ (fun i _ => dz i)
  have hY0 : coordinateProduct (y p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)
  have hZ0 : coordinateProduct (z p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have dPair : AnalyticAt ℂ (fun q => canceledPairProduct (z q) (y q)) p := by
    apply Finset.analyticAt_fun_prod
    intro i _
    apply Finset.analyticAt_fun_prod
    intro j _
    exact (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy i) (hy j)) (pow_ne_zero 2 (hpair i j)))
  have dRes : AnalyticAt ℂ (fun q => ∏ i, residueFactor (z q i)) p := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul ((dz i).pow 2)).div
      (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  have dDensity : AnalyticAt ℂ (fun q => canceledReducedDensity (z q) (y q)) p :=
    ((((dZ.inv hZ0).add (dY.inv hY0)).div
      ((analyticAt_const.sub dZ).mul (analyticAt_const.sub dY))
      (mul_ne_zero hZ hY)).mul dPair).mul dRes
  exact dY.mul dDensity

 def selectedAngularWeight (N : ℕ) (f : SelectorFunctions) (τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ((1-angularSelector f θ:ℝ):ℂ)*(N.factorial:ℂ)⁻¹ *
    (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ))*(angularJacobian f τ 1 θ).det

 theorem selectedAngularWeight_continuous (N : ℕ) (f : SelectorFunctions) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : Continuous f.a) :
    Continuous (selectedAngularWeight N f τ) := by
  have hpd : ContDiff ℝ ∞ (deriv f.p) := by
    apply ContDiff.deriv'
    simpa using hp
  have hmd : ContDiff ℝ ∞ (deriv f.m) := by
    apply ContDiff.deriv'
    simpa using hm
  have hp' := hpd.continuous
  have hm' := hmd.continuous
  have hp0 := hp.continuous
  have hm0 := hm.continuous
  have hJ : Continuous (fun θ : Fin N → ℝ => angularJacobian f τ 1 θ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold angularJacobian retractionJacobian occupancy
    by_cases hij : i=j <;> simp only [hij,ite_true,ite_false] <;> fun_prop
  have ha' : Continuous (fun θ : Fin N → ℝ => angularSelector f θ) := by
    unfold angularSelector selectorWeight
    apply continuous_finsetProd
    intro i _
    fun_prop
  have hdet := hJ.matrix_det
  unfold selectedAngularWeight
  fun_prop

 theorem deformedPoint_continuous {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : Continuous f.p) (hm : Continuous f.m) : Continuous (deformedPoint (N := N) f r τ lam) := by
  apply continuous_pi
  intro i
  unfold deformedPoint retractionShift occupancy
  fun_prop

 theorem continuedSelectedIntegral_eq_supported (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) :
    continuedSelectedIntegral N f r τ s =
      ∫ θ in angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
        selectedAngularWeight N f τ θ * continuedContourDensity N (s,deformedPoint f r τ 1 θ) := by
  unfold continuedSelectedIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _hθ
    dsimp [selectedAngularWeight,continuedContourDensity,continuedPulledDensity]
    ring
  · intro θ hθ
    have hh : θ ∉ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp only [hz,Complex.ofReal_zero,zero_mul]

/-- Geometric pole exclusion suffices for holomorphy of the complete actual
selected integral; there is no hypothesis of a selected-F estimate. -/
theorem continuedSelectedIntegral_analyticOn_of_gaps (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : Continuous f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      ∀ i, sourceW s (deformedPoint f r τ 1 θ i) ∈ continuedRootDomain)
    (hY : ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      1-coordinateProduct (deformedPoint f r τ 1 θ) ≠ 0)
    (hZ : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ 1 θ i)) ≠ 0) :
    AnalyticOnNhd ℂ (continuedSelectedIntegral N f r τ) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (continuedContourDensity N)
    (deformedPoint f r τ 1) (deformedPoint_continuous f r τ 1 hp.continuous hm.continuous)
    (selectedAngularWeight N f τ) (selectedAngularWeight_continuous N f τ hp hm ha)
    (fun t ht θ hθ => continuedContourDensity_analyticAt (hs t ht)
      (deformedPoint_nonzero f hr τ 1 θ) (hW t ht θ hθ) (hY θ hθ) (hZ t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (continuedSelectedIntegral_eq_supported N f r τ t).symm)

end
end IsingBulk.Tail
