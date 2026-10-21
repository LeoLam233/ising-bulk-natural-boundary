import IsingBulk.HT.Contour.OnsiteIntegration
import IsingBulk.Tail.ProtectedDensity

/-! Actual onsite continuation and complete fixed-weight parameter integrals.
Only physical root and pair gaps are needed; no global product gap occurs. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def onsiteContinuedPulledDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ)) *
    (angularJacobian f τ lam θ).det * (∏ i, deformedPoint f r τ lam θ i) *
    onsiteCanceledDensity (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def onsiteContinuedSelectedIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*onsiteContinuedPulledDensity f r τ 1 s θ

theorem onsite_continuedPulledDensity_eq_original {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0 < (sourceW s (deformedPoint f r τ lam θ i)).im) :
    onsiteContinuedPulledDensity f r τ lam s θ = onsitePulledDensity f r τ lam s θ := by
  have he : (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) =
      (fun i => globalRoot s (deformedPoint f r τ lam θ i)) := by
    funext i
    exact continuedRoot_eq_interiorRoot (hW i)
  simp only [onsiteContinuedPulledDensity,onsitePulledDensity,he]


theorem onsite_continuedSelectedIntegral_eventually_original (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    {s : ℂ} (hmarg : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    onsiteContinuedSelectedIntegral N f r τ =ᶠ[𝓝 s] onsiteSelectedIntegral N f r τ := by
  have hsD := dampingDomain_of_margin hr hr1 hmarg
  filter_upwards [dampingDomain_mem_nhds hsD] with t ht
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_Icc)
  intro θ _hθ
  dsimp only
  congr 1
  apply onsite_continuedPulledDensity_eq_original
  intro i
  exact (sourceW_upper_of_margin hr hr1 ht.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ (by norm_num) θ t hp hm0 hps hms i)

 def onsiteContinuedContourDensity (N : ℕ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, p.2 i)*onsiteCanceledDensity (fun i => selectedContinuedRoot p.1 (p.2 i)) p.2

 theorem onsite_continuedContourDensity_analyticAt {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (hs : p.1 ≠ 0) (hy : ∀ i, p.2 i ≠ 0)
    (hW : ∀ i, sourceW p.1 (p.2 i) ∈ continuedRootDomain) :
    AnalyticAt ℂ (onsiteContinuedContourDensity N) p := by
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
  have dDensity : AnalyticAt ℂ (fun q => onsiteCanceledDensity (z q) (y q)) p :=
    (((dZ.mul dY).inv (mul_ne_zero hZ0 hY0)).mul dPair).mul dRes
  exact dY.mul dDensity


 theorem onsite_continuedSelectedIntegral_eq_supported (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) :
    onsiteContinuedSelectedIntegral N f r τ s =
      ∫ θ in angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
        selectedAngularWeight N f τ θ * onsiteContinuedContourDensity N (s,deformedPoint f r τ 1 θ) := by
  unfold onsiteContinuedSelectedIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _hθ
    dsimp [selectedAngularWeight,onsiteContinuedContourDensity,onsiteContinuedPulledDensity]
    ring
  · intro θ hθ
    have hh : θ ∉ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp only [hz,Complex.ofReal_zero,zero_mul]

/-- Geometric pole exclusion suffices for holomorphy of the complete actual
selected integral; there is no hypothesis of a selected-F estimate. -/
theorem onsite_continuedSelectedIntegral_analyticOn_of_roots (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : Continuous f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      ∀ i, sourceW s (deformedPoint f r τ 1 θ i) ∈ continuedRootDomain) :
    AnalyticOnNhd ℂ (onsiteContinuedSelectedIntegral N f r τ) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (onsiteContinuedContourDensity N)
    (deformedPoint f r τ 1) (deformedPoint_continuous f r τ 1 hp.continuous hm.continuous)
    (selectedAngularWeight N f τ) (selectedAngularWeight_continuous N f τ hp hm ha)
    (fun t ht θ hθ => onsite_continuedContourDensity_analyticAt (hs t ht)
      (deformedPoint_nonzero f hr τ 1 θ) (hW t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (onsite_continuedSelectedIntegral_eq_supported N f r τ t).symm)

def onsiteContinuedNamedCurrentDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*onsiteContinuedPulledDensity f r τ lam s θ


def onsiteContinuedNamedCurrentIntegral (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, onsiteContinuedNamedCurrentDensity f r τ lam s q θ

def onsiteActualNamedCurrentIntegral (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, onsiteNamedCurrentDensity f r τ lam s q θ

def onsiteContinuedCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, onsiteContinuedNamedCurrentIntegral N f r τ lam q s

def onsiteActualCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, onsiteActualNamedCurrentIntegral N f r τ lam q s


theorem onsite_continuedNamedCurrentDensity_weighted {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) :
    onsiteContinuedNamedCurrentDensity f r τ lam s q θ =
      namedCurrentAngularWeight N f τ lam q θ *
        onsiteContinuedContourDensity N (s,deformedPoint f r τ lam θ) := by
  unfold onsiteContinuedNamedCurrentDensity namedCurrentAngularWeight onsiteContinuedPulledDensity onsiteContinuedContourDensity
  ring

theorem onsite_continuedPulledDensity_analyticAt {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun z => onsiteContinuedPulledDensity f r τ lam z θ) s := by
  have ha₀ : AnalyticAt ℂ (onsiteContinuedContourDensity N) (s,deformedPoint f r τ lam θ) :=
    onsite_continuedContourDensity_analyticAt (p := (s,deformedPoint f r τ lam θ)) hs
      (deformedPoint_nonzero f hr τ lam θ) hW
  have hmap : AnalyticAt ℂ (fun z : ℂ => (z,deformedPoint f r τ lam θ)) s :=
    analyticAt_id.prod analyticAt_const
  have ha := ha₀.comp (f := fun z : ℂ => (z,deformedPoint f r τ lam θ)) hmap
  have he : (fun z => onsiteContinuedPulledDensity f r τ lam z θ) =
      (fun z => ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det)*onsiteContinuedContourDensity N (z,deformedPoint f r τ lam θ)) := by
    funext z
    unfold onsiteContinuedPulledDensity onsiteContinuedContourDensity
    ring
  rw [he]
  exact analyticAt_const.mul ha

theorem onsite_continuedNamedCurrentDensity_analyticAt {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
    {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun z => onsiteContinuedNamedCurrentDensity f r τ lam z q θ) s :=
  analyticAt_const.mul (onsite_continuedPulledDensity_analyticAt f hr τ lam θ hs hW)


theorem onsite_continuedNamedCurrentIntegral_eq_supported (N : ℕ) (f : SelectorFunctions)
    (r τ lam : ℝ) (q : Fin N) (s : ℂ) :
    onsiteContinuedNamedCurrentIntegral N f r τ lam q s =
      ∫ θ in angleBox N ∩ tsupport (namedSelectorDerivative f q),
        namedCurrentAngularWeight N f τ lam q θ *
          onsiteContinuedContourDensity N (s,deformedPoint f r τ lam θ) := by
  unfold onsiteContinuedNamedCurrentIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (namedSelectorDerivative f q))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _
    exact onsite_continuedNamedCurrentDensity_weighted f r τ lam s q θ
  · intro θ hθ
    have hh : θ ∉ tsupport (namedSelectorDerivative f q) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp [onsiteContinuedNamedCurrentDensity,hz]

theorem onsite_continuedNamedCurrentIntegral_analyticOn_of_roots (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain) :
    AnalyticOnNhd ℂ (onsiteContinuedNamedCurrentIntegral N f r τ lam q) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (namedSelectorDerivative f q)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (onsiteContinuedContourDensity N)
    (deformedPoint f r τ lam) (deformedPoint_continuous f r τ lam hp.continuous hm.continuous)
    (namedCurrentAngularWeight N f τ lam q) (namedCurrentAngularWeight_continuous N f τ lam q hp hm ha)
    (fun t ht θ hθ => onsite_continuedContourDensity_analyticAt (hs t ht)
      (deformedPoint_nonzero f hr τ lam θ) (hW t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (onsite_continuedNamedCurrentIntegral_eq_supported N f r τ lam q t).symm)

/-- Literal source derivative slice, before any lambda split. -/
def onsiteDifferentiatedCurrentSlice (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (j : ℕ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, ∫ θ in angleBox N,
    iteratedDeriv j (fun z => onsiteNamedCurrentDensity f r τ lam z q θ) s

theorem onsite_continuedCurrentSlice_eventually_actual (N : ℕ) (hN : 0 < N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    onsiteContinuedCurrentSlice N f r τ lam =ᶠ[𝓝 s] onsiteActualCurrentSlice N f r τ lam := by
  have hsD := dampingDomain_of_margin hr hr1 hmargin
  filter_upwards [dampingDomain_mem_nhds hsD] with z hz
  apply Finset.sum_congr rfl
  intro q _
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  unfold onsiteContinuedNamedCurrentDensity onsiteNamedCurrentDensity
  rw [onsite_continuedPulledDensity_eq_original f r τ lam z θ]
  intro i
  exact (sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ hlam θ z hp0 hm0 hps hms i)

/-- The current multiplier is fixed during every temperature derivative. -/
theorem onsiteDifferentiatedCurrentSlice_source_formula (N : ℕ)
    (f : SelectorFunctions) (r τ lam : ℝ) (j : ℕ) (s : ℂ) :
    onsiteDifferentiatedCurrentSlice N f r τ lam j s =
      ∑ q : Fin N, ∫ θ in angleBox N,
        (-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ))*
          iteratedDeriv j (fun z => onsitePulledDensity f r τ lam z θ) s := by
  unfold onsiteDifferentiatedCurrentSlice onsiteNamedCurrentDensity
  simp only [iteratedDeriv_const_mul_field]

end
end IsingBulk.HT.Contour
