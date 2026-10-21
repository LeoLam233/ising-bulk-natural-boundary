import IsingBulk.HT.Contour.SignedIntegration
import IsingBulk.Tail.ProtectedDensity

/-! Literal signed continuations with the same fixed real angular weights.
Holomorphy is proved on the actual root/gap domain, never on a cutoff
assignment or an assumed source estimate. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def signedContinuedPulledDensity (σ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ)) *
    (angularJacobian f τ lam θ).det * (∏ i, deformedPoint f r τ lam θ i) *
    signedCanceledDensity σ (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def signedContinuedSelectedIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*signedContinuedPulledDensity σ f r τ 1 s θ

theorem signed_continuedPulledDensity_eq_original (σ : ℂ) {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0 < (sourceW s (deformedPoint f r τ lam θ i)).im) :
    signedContinuedPulledDensity σ f r τ lam s θ = signedPulledDensity σ f r τ lam s θ := by
  have he : (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) =
      (fun i => globalRoot s (deformedPoint f r τ lam θ i)) := by
    funext i
    exact continuedRoot_eq_interiorRoot (hW i)
  simp only [signedContinuedPulledDensity,signedPulledDensity,he]


theorem signed_continuedSelectedIntegral_eventually_original (σ : ℂ) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    {s : ℂ} (hmarg : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    signedContinuedSelectedIntegral σ N f r τ =ᶠ[𝓝 s] signedSelectedIntegral σ N f r τ := by
  have hsD := dampingDomain_of_margin hr hr1 hmarg
  filter_upwards [dampingDomain_mem_nhds hsD] with t ht
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_Icc)
  intro θ _hθ
  dsimp only
  congr 1
  apply signed_continuedPulledDensity_eq_original σ
  intro i
  exact (sourceW_upper_of_margin hr hr1 ht.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ (by norm_num) θ t hp hm0 hps hms i)

 def signedContinuedContourDensity (σ : ℂ) (N : ℕ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, p.2 i)*signedCanceledDensity σ (fun i => selectedContinuedRoot p.1 (p.2 i)) p.2

 theorem signed_continuedContourDensity_analyticAt (σ : ℂ) {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (hs : p.1 ≠ 0) (hy : ∀ i, p.2 i ≠ 0)
    (hW : ∀ i, sourceW p.1 (p.2 i) ∈ continuedRootDomain)
    (hY : 1-σ*coordinateProduct p.2 ≠ 0)
    (hZ : 1-σ*coordinateProduct (fun i => selectedContinuedRoot p.1 (p.2 i)) ≠ 0) :
    AnalyticAt ℂ (signedContinuedContourDensity σ N) p := by
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
  have dDensity : AnalyticAt ℂ (fun q => signedCanceledDensity σ (z q) (y q)) p :=
    ((((dZ.inv hZ0).add (dY.inv hY0)).div
      ((analyticAt_const.sub (analyticAt_const.mul dZ)).mul (analyticAt_const.sub (analyticAt_const.mul dY)))
      (mul_ne_zero hZ hY)).mul dPair).mul dRes
  exact dY.mul dDensity


 theorem signed_continuedSelectedIntegral_eq_supported (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) :
    signedContinuedSelectedIntegral σ N f r τ s =
      ∫ θ in angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
        selectedAngularWeight N f τ θ * signedContinuedContourDensity σ N (s,deformedPoint f r τ 1 θ) := by
  unfold signedContinuedSelectedIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _hθ
    dsimp [selectedAngularWeight,signedContinuedContourDensity,signedContinuedPulledDensity]
    ring
  · intro θ hθ
    have hh : θ ∉ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp only [hz,Complex.ofReal_zero,zero_mul]

/-- Geometric pole exclusion suffices for holomorphy of the complete actual
selected integral; there is no hypothesis of a selected-F estimate. -/
theorem signed_continuedSelectedIntegral_analyticOn_of_gaps (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : Continuous f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      ∀ i, sourceW s (deformedPoint f r τ 1 θ i) ∈ continuedRootDomain)
    (hY : ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      1-σ*coordinateProduct (deformedPoint f r τ 1 θ) ≠ 0)
    (hZ : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ),
      1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ 1 θ i)) ≠ 0) :
    AnalyticOnNhd ℂ (signedContinuedSelectedIntegral σ N f r τ) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (signedContinuedContourDensity σ N)
    (deformedPoint f r τ 1) (deformedPoint_continuous f r τ 1 hp.continuous hm.continuous)
    (selectedAngularWeight N f τ) (selectedAngularWeight_continuous N f τ hp hm ha)
    (fun t ht θ hθ => signed_continuedContourDensity_analyticAt σ (hs t ht)
      (deformedPoint_nonzero f hr τ 1 θ) (hW t ht θ hθ) (hY θ hθ) (hZ t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (signed_continuedSelectedIntegral_eq_supported σ N f r τ t).symm)

def signedContinuedNamedCurrentDensity (σ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*signedContinuedPulledDensity σ f r τ lam s θ


def signedContinuedNamedCurrentIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, signedContinuedNamedCurrentDensity σ f r τ lam s q θ

def signedActualNamedCurrentIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (q : Fin N) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, signedNamedCurrentDensity σ f r τ lam s q θ

def signedContinuedCurrentSlice (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, signedContinuedNamedCurrentIntegral σ N f r τ lam q s

def signedActualCurrentSlice (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, signedActualNamedCurrentIntegral σ N f r τ lam q s


theorem signed_continuedNamedCurrentDensity_weighted (σ : ℂ) {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) :
    signedContinuedNamedCurrentDensity σ f r τ lam s q θ =
      namedCurrentAngularWeight N f τ lam q θ *
        signedContinuedContourDensity σ N (s,deformedPoint f r τ lam θ) := by
  unfold signedContinuedNamedCurrentDensity namedCurrentAngularWeight signedContinuedPulledDensity signedContinuedContourDensity
  ring

theorem signed_continuedPulledDensity_analyticAt (σ : ℂ) {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : 1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : 1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticAt ℂ (fun z => signedContinuedPulledDensity σ f r τ lam z θ) s := by
  have ha₀ : AnalyticAt ℂ (signedContinuedContourDensity σ N) (s,deformedPoint f r τ lam θ) :=
    signed_continuedContourDensity_analyticAt σ (p := (s,deformedPoint f r τ lam θ)) hs
      (deformedPoint_nonzero f hr τ lam θ) hW hY hZ
  have hmap : AnalyticAt ℂ (fun z : ℂ => (z,deformedPoint f r τ lam θ)) s :=
    analyticAt_id.prod analyticAt_const
  have ha := ha₀.comp (f := fun z : ℂ => (z,deformedPoint f r τ lam θ)) hmap
  have he : (fun z => signedContinuedPulledDensity σ f r τ lam z θ) =
      (fun z => ((N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det)*signedContinuedContourDensity σ N (z,deformedPoint f r τ lam θ)) := by
    funext z
    unfold signedContinuedPulledDensity signedContinuedContourDensity
    ring
  rw [he]
  exact analyticAt_const.mul ha

theorem signed_continuedNamedCurrentDensity_analyticAt (σ : ℂ) {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
    {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : 1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : 1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticAt ℂ (fun z => signedContinuedNamedCurrentDensity σ f r τ lam z q θ) s :=
  analyticAt_const.mul (signed_continuedPulledDensity_analyticAt σ f hr τ lam θ hs hW hY hZ)


theorem signed_continuedNamedCurrentIntegral_eq_supported (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    (r τ lam : ℝ) (q : Fin N) (s : ℂ) :
    signedContinuedNamedCurrentIntegral σ N f r τ lam q s =
      ∫ θ in angleBox N ∩ tsupport (namedSelectorDerivative f q),
        namedCurrentAngularWeight N f τ lam q θ *
          signedContinuedContourDensity σ N (s,deformedPoint f r τ lam θ) := by
  unfold signedContinuedNamedCurrentIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := angleBox N ∩ tsupport (namedSelectorDerivative f q))
    (t := angleBox N) measurableSet_Icc inter_subset_left]
  · apply setIntegral_congr_fun (measurableSet_Icc.inter (isClosed_tsupport _).measurableSet)
    intro θ _
    exact signed_continuedNamedCurrentDensity_weighted σ f r τ lam s q θ
  · intro θ hθ
    have hh : θ ∉ tsupport (namedSelectorDerivative f q) := by
      intro ht
      exact hθ.2 ⟨hθ.1,ht⟩
    have hz := image_eq_zero_of_notMem_tsupport hh
    simp [signedContinuedNamedCurrentDensity,hz]

theorem signed_continuedNamedCurrentIntegral_analyticOn_of_gaps (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    {U : Set ℂ} (hU : IsOpen U) (hs : ∀ s ∈ U, s ≠ 0)
    (hW : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : ∀ s ∈ U, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    AnalyticOnNhd ℂ (signedContinuedNamedCurrentIntegral σ N f r τ lam q) U := by
  intro s hsU
  have hK : IsCompact (angleBox N ∩ tsupport (namedSelectorDerivative f q)) :=
    isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc := compact_analytic_shape_integral_analyticAt (μ := volume) hK hU (signedContinuedContourDensity σ N)
    (deformedPoint f r τ lam) (deformedPoint_continuous f r τ lam hp.continuous hm.continuous)
    (namedCurrentAngularWeight N f τ lam q) (namedCurrentAngularWeight_continuous N f τ lam q hp hm ha)
    (fun t ht θ hθ => signed_continuedContourDensity_analyticAt σ (hs t ht)
      (deformedPoint_nonzero f hr τ lam θ) (hW t ht θ hθ) (hY θ hθ) (hZ t ht θ hθ)) hsU
  apply hc.congr
  exact Filter.Eventually.of_forall (fun t => (signed_continuedNamedCurrentIntegral_eq_supported σ N f r τ lam q t).symm)

/-- Literal source derivative slice, before any lambda split. -/
def signedDifferentiatedCurrentSlice (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (j : ℕ) (s : ℂ) : ℂ :=
  ∑ q : Fin N, ∫ θ in angleBox N,
    iteratedDeriv j (fun z => signedNamedCurrentDensity σ f r τ lam z q θ) s

theorem signed_continuedCurrentSlice_eventually_actual (σ : ℂ) (N : ℕ) (hN : 0 < N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    signedContinuedCurrentSlice σ N f r τ lam =ᶠ[𝓝 s] signedActualCurrentSlice σ N f r τ lam := by
  have hsD := dampingDomain_of_margin hr hr1 hmargin
  filter_upwards [dampingDomain_mem_nhds hsD] with z hz
  apply Finset.sum_congr rfl
  intro q _
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  unfold signedContinuedNamedCurrentDensity signedNamedCurrentDensity
  rw [signed_continuedPulledDensity_eq_original σ f r τ lam z θ]
  intro i
  exact (sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ hlam θ z hp0 hm0 hps hms i)

/-- The current multiplier is fixed during every temperature derivative. -/
theorem signedDifferentiatedCurrentSlice_source_formula (σ : ℂ) (N : ℕ)
    (f : SelectorFunctions) (r τ lam : ℝ) (j : ℕ) (s : ℂ) :
    signedDifferentiatedCurrentSlice σ N f r τ lam j s =
      ∑ q : Fin N, ∫ θ in angleBox N,
        (-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ))*
          iteratedDeriv j (fun z => signedPulledDensity σ f r τ lam z θ) s := by
  unfold signedDifferentiatedCurrentSlice signedNamedCurrentDensity
  simp only [iteratedDeriv_const_mul_field]

end
end IsingBulk.HT.Contour
