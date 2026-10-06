import IsingBulk.Analysis.JetsJacobian
import IsingBulk.Analysis.JetsRegularKernel

/-! Differential chain rules for the actual chart. These keep the real
angular domain separate from the analytic regular coordinates. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Lie
open scoped BigOperators

def chartMap {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) : Fin (n+1) → ℂ :=
  fun i => chartPhase s v θ (x i)

def chartSpatialMap {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) :
    AngularSpace n →L[ℝ] (Fin (n+1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℝ) i).smulRight (chartB s v θ (x i))

theorem chartMap_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    HasFDerivAt (chartMap v θ s) (chartSpatialMap v θ s x) x := by
  exact hasFDerivAt_pi.mpr fun i => coordinate_hasFDerivAt _ _ x i
    (chartPhase_real_angular s v θ (x i) (hr i) (hi i))

theorem chartMap_parameter {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    HasDerivAt (fun t => chartMap v θ t x) (fun i => chartTau s v θ (x i)) s :=
  hasDerivAt_pi.mpr fun i => chartPhase_parameter s v θ (x i) hs (hr i) (hi i)

theorem chartSpatialMap_single {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) (i : Fin (n+1)) :
    chartSpatialMap v θ s x (Pi.single i 1) = Pi.single i (chartB s v θ (x i)) := by
  ext k
  by_cases h : k = i
  · subst k; simp [chartSpatialMap]
  · simp [chartSpatialMap, h]

theorem chart_composition_parameter {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    deriv (fun t => F t (chartMap v θ t x)) s =
      fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x)
        (1,fun i => chartTau s v θ (x i)) := by
  have hh := hF.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))
  convert! hh.deriv using 1

theorem chart_composition_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) (i : Fin (n+1)) :
    fderiv ℝ (fun y => F s (chartMap v θ s y)) x (Pi.single i 1) =
      fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x)
        (0,Pi.single i (chartB s v θ (x i))) := by
  have hh := ((hF.hasFDerivAt.restrictScalars ℝ).comp x
    ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))).fderiv
  change fderiv ℝ (fun y => F s (chartMap v θ s y)) x = _ at hh
  rw [hh]
  change fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x)
    (0,chartSpatialMap v θ s x (Pi.single i 1)) = _
  rw [chartSpatialMap_single]

theorem chart_transport_chain {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    transport (actualField v θ p q) (fun t y => F t (chartMap v θ t y)) s x =
      regularTransport p q F s (chartMap v θ s x) := by
  rw [regularTransport_fderiv p q F s _ hF]
  unfold transport
  rw [chart_composition_parameter v θ s x F hs hr hi hF]
  simp_rw [chart_composition_spatial v θ s x F hr hi hF]
  let L := fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x)
  change L (1,fun i => chartTau s v θ (x i)) -
    (∑ i, actualField v θ p q s x i*L (0,Pi.single i (chartB s v θ (x i)))) = _
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, ← map_sub]
  congr 1
  apply Prod.ext
  · change (1:ℂ)-(ContinuousLinearMap.fst ℂ ℂ (Fin (n+1) → ℂ))
      (∑ i, actualField v θ p q s x i • (0,Pi.single i (chartB s v θ (x i)))) = 1
    rw [map_sum]; simp
  · rw [show regularResidualField p q s (chartMap v θ s x) = actualResidual v θ p q s x from
      regularResidualField_chart p q v θ s x hs hr hi hg]
    change (fun i => chartTau s v θ (x i))-
      (ContinuousLinearMap.snd ℂ ℂ (Fin (n+1) → ℂ))
        (∑ i, actualField v θ p q s x i • (0,Pi.single i (chartB s v θ (x i)))) = _
    rw [map_sum]
    funext i
    simp [Pi.single_apply, Finset.sum_apply, actualResidual,
      (chartPhase_parameter s v θ (x i) hs (hr i) (hi i)).deriv, chartTau, mul_comm]

theorem chart_regular_locus_eventually {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    ∀ᶠ y in nhds x, (∀ i, 0 < (chartW s v θ (y i)).re) ∧
      (∀ i, 0 < (chartW s v θ (y i)).im) ∧ (∀ i, 0 < (angularG v θ (y i)).re) := by
  have hW : ∀ i, ContinuousAt (fun y : AngularSpace n => chartW s v θ (y i)) x := by
    intro i
    have hof : ContinuousAt (fun y : AngularSpace n => (y i:ℂ)) x :=
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) i)).continuous.continuousAt
    exact (chartW_angular s v θ (x i)).continuousAt.comp
      (f := fun y : AngularSpace n => (y i:ℂ)) hof
  have hG : ∀ i, ContinuousAt (fun y : AngularSpace n => angularG v θ (y i)) x := by
    intro i
    have hof : ContinuousAt (fun y : AngularSpace n => (y i:ℂ)) x :=
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) i)).continuous.continuousAt
    exact (angularG_hasDerivAt v θ (x i)).continuousAt.comp
      (f := fun y : AngularSpace n => (y i:ℂ)) hof
  exact (Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
    (Complex.continuous_re.continuousAt.comp (hW i)) (hr i))).and
    ((Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
      (Complex.continuous_im.continuousAt.comp (hW i)) (hi i))).and
      (Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
        (Complex.continuous_re.continuousAt.comp (hG i)) (hg i))))

theorem residual_chart_spatial {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (i : Fin (n+1)) (hs : s ≠ 0)
    (hr : ∀ k, 0 < (chartW s v θ (x k)).re)
    (hi : ∀ k, 0 < (chartW s v θ (x k)).im)
    (hg : ∀ k, 0 < (angularG v θ (x k)).re)
    (hn : Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hV : DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x)
    (hB : DifferentiableAt ℂ
      (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i) (s,chartMap v θ s x)) :
    chartB s v θ (x i)*
      fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i)
        (s,chartMap v θ s x) (spatialDirection i) =
      chartMixed s v θ (x i) - chartSpatialB s v θ (x i)*actualField v θ p q s x i -
        chartB s v θ (x i)*fderiv ℝ (fun y => actualField v θ p q s y i) x (Pi.single i 1) := by
  have he : (fun y : AngularSpace n => regularResidualField p q s (chartMap v θ s y) i) =ᶠ[nhds x]
      (fun y => chartTau s v θ (y i)-chartB s v θ (y i)*actualField v θ p q s y i) := by
    filter_upwards [chart_regular_locus_eventually v θ s x hr hi hg] with y hy
    rw [show regularResidualField p q s (chartMap v θ s y) = actualResidual v θ p q s y from
      regularResidualField_chart p q v θ s y hs hy.1 hy.2.1 hy.2.2]
    rw [actualResidual, (chartPhase_parameter s v θ (y i) hs (hy.1 i) (hy.2.1 i)).deriv]
    rfl
  have hτ := coordinate_hasFDerivAt _ _ x i
    ((chartTau_angular s v θ (x i) (hr i) (hi i) hn).comp_ofReal)
  have hb := coordinate_hasFDerivAt _ _ x i
    ((chartB_angular s v θ (x i) (hr i) (hi i) hn).comp_ofReal)
  have hh := (hτ.fun_sub (hb.fun_mul hV.hasFDerivAt)).fderiv
  have hc := chart_composition_spatial v θ s x
    (fun t ψ => regularResidualField p q t ψ i) hr hi hB i
  rw [he.fderiv_eq, hh] at hc
  have hv : ((0:ℂ),Pi.single i (chartB s v θ (x i))) =
      chartB s v θ (x i) • spatialDirection i := by
    ext k <;> simp [spatialDirection, Pi.single_apply, mul_ite]
  rw [hv, map_smul] at hc
  simpa [smul_eq_mul, mul_comm, sub_sub, add_comm] using hc.symm

theorem chartJacobian_lie {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x)
    (hB : ∀ i, DifferentiableAt ℂ
      (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i) (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (chartJacobian v θ) s x =
      chartJacobian v θ s x*residualDivergence p q (s,chartMap v θ s x) := by
  rw [lieStep_eq_transport_sub _ _ s x hV (chartJacobian_spatial v θ s x hr hi hn).differentiableAt]
  unfold transport divergence residualDivergence
  rw [(chartJacobian_parameter v θ s x hs hr hi hn).deriv]
  simp_rw [chartJacobian_spatial_apply v θ s x hr hi hn]
  rw [Finset.mul_sum]
  have he : ∀ i, chartJacobian v θ s x *
      fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i)
        (s,chartMap v θ s x) (spatialDirection i) =
      (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k)) *
        (chartMixed s v θ (x i)-chartSpatialB s v θ (x i)*actualField v θ p q s x i) -
          chartJacobian v θ s x*fderiv ℝ (fun y => actualField v θ p q s y i) x (Pi.single i 1) := by
    intro i
    have hprod : chartJacobian v θ s x =
        (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*chartB s v θ (x i) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hprod, mul_assoc, residual_chart_spatial v θ p q s x i hs hr hi hg (hn i) (hV i) (hB i)]
    ring
  simp_rw [he]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [mul_assoc, mul_comm]

def regularDensityStep {N : ℕ} (p q : Fin N) (F : ℂ → (Fin N → ℂ) → ℂ)
    (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  regularTransport p q F s φ + residualDivergence p q (s,φ)*F s φ

/-- Unweighted top-form pullback: J is the actual diagonal chart Jacobian,
and the residual is constructed from the actual selected-pair formulas. -/
theorem chartPullback_lie {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x)
    (hB : ∀ i, DifferentiableAt ℂ
      (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i) (s,chartMap v θ s x))
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (chartPullback v θ F) s x =
      chartPullback v θ (regularDensityStep p q F) s x := by
  have hFs : DifferentiableAt ℂ (fun t => F t (chartMap v θ t x)) s := by
    have hh := (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))).differentiableAt
    convert! hh using 1
  have hFx : DifferentiableAt ℝ (fun y => F s (chartMap v θ s y)) x := by
    have hh := ((hF.hasFDerivAt.restrictScalars ℝ).comp x
      ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))).differentiableAt
    convert! hh using 1
  have he : chartPullback v θ F = fun t y => F t (chartMap v θ t y)*chartJacobian v θ t y := by
    funext t y; exact mul_comm _ _
  rw [he, lieStep_product_rule _ _ _ s x hFs
    (chartJacobian_parameter v θ s x hs hr hi hn).differentiableAt hFx
    (chartJacobian_spatial v θ s x hr hi hn).differentiableAt hV]
  rw [chartJacobian_lie v θ p q s x hs hr hi hg hn hV hB,
    chart_transport_chain v θ p q s x F hs hr hi hg hF]
  change _ = chartJacobian v θ s x *
    (regularTransport p q F s (chartMap v θ s x) +
      residualDivergence p q (s,chartMap v θ s x)*F s (chartMap v θ s x))
  ring

/-- eq:pullbackLie on the original real domain. All hypotheses are local
regularity or chart-domain conditions; neither side of the identity is a
caller premise, and w has only a real derivative. -/
theorem pullbackLie_real_weight {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (w : AngularSpace n → ℝ)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x)
    (hB : ∀ i, DifferentiableAt ℂ
      (fun z : ℂ × (Fin (n+1) → ℂ) => regularResidualField p q z.1 z.2 i) (s,chartMap v θ s x))
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) (hw : DifferentiableAt ℝ w x) :
    lieStep (actualField v θ p q) (fun t y => (w y:ℂ)*chartPullback v θ F t y) s x =
      (w x:ℂ)*chartPullback v θ (regularDensityStep p q F) s x -
        (∑ i, actualField v θ p q s x i*(fderiv ℝ w x (Pi.single i 1):ℂ))*
          chartPullback v θ F s x := by
  have hFs : DifferentiableAt ℂ (fun t => F t (chartMap v θ t x)) s := by
    have hh := (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))).differentiableAt
    convert! hh using 1
  have hFx : DifferentiableAt ℝ (fun y => F s (chartMap v θ s y)) x := by
    have hh := ((hF.hasFDerivAt.restrictScalars ℝ).comp x
      ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))).differentiableAt
    convert! hh using 1
  have hPs := (chartJacobian_parameter v θ s x hs hr hi hn).differentiableAt.mul hFs
  have hPx := (chartJacobian_spatial v θ s x hr hi hn).differentiableAt.mul hFx
  rw [chartPullback_real_cutoff v θ p q w F s x hw hPs hPx hV,
    chartPullback_lie v θ p q s x F hs hr hi hg hn hV hB hF]

theorem actualField_differentiable {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hd : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0) (i : Fin (n+1)) :
    DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x := by
  have hA : ∀ k, DifferentiableAt ℝ (fun y : AngularSpace n => chartA s v θ (y k)) x := by
    intro k
    have hh := (hasDerivAt_const (x k:ℂ) (sourceSPrime s)).div
      (angularG_hasDerivAt v θ (x k)).neg (neg_ne_zero.mpr (hg k))
    exact (coordinate_hasFDerivAt _ _ x k hh.comp_ofReal).differentiableAt
  have hb : ∀ k, DifferentiableAt ℝ (fun y : AngularSpace n => chartB s v θ (y k)) x := by
    intro k
    exact (coordinate_hasFDerivAt _ _ x k
      ((chartB_angular s v θ (x k) (hr k) (hi k) (hn k)).comp_ofReal)).differentiableAt
  have haSum : DifferentiableAt ℝ (fun y : AngularSpace n => ∑ k, chartA s v θ (y k)) x :=
    DifferentiableAt.fun_sum fun k _ => hA k
  have hpt := (haSum.mul (hb q)).mul (((hb p).sub (hb q)).inv hd)
  have hqt := (haSum.mul (hb p)).mul (((hb p).sub (hb q)).inv hd)
  unfold actualField selectedField
  simp only [div_eq_mul_inv]
  split_ifs
  · exact ((hA i).add hpt).sub hqt
  · exact ((hA i).add hpt).sub_const 0
  · exact ((hA i).add_const 0).sub hqt
  · exact ((hA i).add_const 0).sub_const 0

theorem regularResidualField_analytic {N : ℕ} (p q i : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hs : s ≠ 0) (hslit : ∀ k, 1-(s+s⁻¹-Complex.cos (φ k))^2 ∈ Complex.slitPlane)
    (hg : ∀ k, regularG s (φ k) ≠ 0) (hn : ∀ k, Complex.sin (φ k) ≠ 0)
    (hd : regularB s (φ p)-regularB s (φ q) ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularResidualField p q z.1 z.2 i) (s,φ) := by
  have hG : ∀ k, AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularG z.1 (z.2 k)) (s,φ) := by
    intro k
    have hy := AnalyticAt.comp (g := fun z : ℂ × ℂ => Branch.regularY z.1 z.2)
      (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 k))
      (x := (s,φ))
      (Branch.regularY_analytic s (φ k) hs (hslit k))
      (analyticAt_fst.prod (analytic_coordinate k _))
    exact (analyticAt_const.mul (hy.sub (hy.inv (Branch.regularY_ne_zero s (φ k))))).div_const
  have hsin : ∀ k, AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => Complex.sin (z.2 k)) (s,φ) :=
    fun k => Complex.analyticAt_sin.comp (analytic_coordinate k _)
  have hA : ∀ k, AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularA z.1 (z.2 k)) (s,φ) := by
    intro k
    apply AnalyticAt.div
    · exact analyticAt_const.sub ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 hs))
    · exact (hG k).neg
    · exact neg_ne_zero.mpr (hg k)
  have hb : ∀ k, AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularB z.1 (z.2 k)) (s,φ) :=
    fun k => (hG k).div (hsin k) (hn k)
  have haSum : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => ∑ k, regularA z.1 (z.2 k)) (s,φ) :=
    Finset.analyticAt_fun_sum _ fun k _ => hA k
  unfold regularResidualField residualField selectedField
  split_ifs <;> fun_prop (disch := exact hd)

/-- The density operator is precisely parameter differentiation plus the
coordinate coefficient of Lie_B on a top form, namely div(B F). -/
theorem regularDensityStep_eq_divergence {N : ℕ} (p q : Fin N)
    (F : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ))
    (hB : ∀ i, DifferentiableAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => regularResidualField p q z.1 z.2 i) (s,φ)) :
    regularDensityStep p q F s φ = deriv (fun t => F t φ) s +
      ∑ i, fderiv ℂ (fun ψ => regularResidualField p q s ψ i*F s ψ) φ (Pi.single i 1) := by
  have hFx : DifferentiableAt ℂ (F s) φ := by
    have hh := hF.hasFDerivAt.comp φ ((hasFDerivAt_const s φ).prodMk (hasFDerivAt_id φ))
    convert! hh.differentiableAt using 1
  have hBx : ∀ i, DifferentiableAt ℂ (fun ψ => regularResidualField p q s ψ i) φ := by
    intro i
    have hh := (hB i).hasFDerivAt.comp φ ((hasFDerivAt_const s φ).prodMk (hasFDerivAt_id φ))
    convert! hh.differentiableAt using 1
  rw [regularDensityStep, regularTransport_eq_partials p q F s φ hF]
  unfold residualDivergence
  simp_rw [joint_spatial_eq _ s φ _ (hB _), fderiv_fun_mul (hBx _) hFx]
  simp only [add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [mul_comm, add_assoc]

/-- The actual selected formulas supply field regularity. The remaining
hypotheses describe the local chart and the coefficient being pulled back. -/
theorem pullbackLie_selected {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (w : AngularSpace n → ℝ)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hd : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0)
    (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (chartPhase s v θ (x i)))^2 ∈ Complex.slitPlane)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) (hw : DifferentiableAt ℝ w x) :
    lieStep (actualField v θ p q) (fun t y => (w y:ℂ)*chartPullback v θ F t y) s x =
      (w x:ℂ)*chartPullback v θ (regularDensityStep p q F) s x -
        (∑ i, actualField v θ p q s x i*(fderiv ℝ w x (Pi.single i 1):ℂ))*
          chartPullback v θ F s x := by
  have hgz : ∀ i, angularG v θ (x i) ≠ 0 := fun i h => by simpa [h] using hg i
  have hgr : ∀ i, regularG s (chartMap v θ s x i) ≠ 0 := by
    intro i
    rw [chartMap, regularG_chartPhase s v θ (x i) (hg i)]
    exact hgz i
  have hdr : regularB s (chartMap v θ s x p)-regularB s (chartMap v θ s x q) ≠ 0 := by
    simpa only [chartMap, regularB_chartPhase s v θ _ (hg _)] using hd
  exact pullbackLie_real_weight v θ p q s x w F hs hr hi hg hn
    (actualField_differentiable v θ p q s x hr hi hgz hn hd)
    (fun i => (regularResidualField_analytic p q i s (chartMap v θ s x) hs hslit hgr hn hdr).differentiableAt)
    hF hw

end
end IsingBulk.Jets


