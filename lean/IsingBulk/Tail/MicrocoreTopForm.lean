import IsingBulk.Tail.MicrocoreTransport

/-! Exact diagonal-Jacobian cancellation for the one-phase microcore field.
The full top form is transported on the fixed real angular domain. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie Filter
open scoped BigOperators Topology

theorem chartA_differentiableAt (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : angularG v θ u ≠ 0) : DifferentiableAt ℂ (chartA s v θ) u := by
  exact (differentiableAt_const (sourceSPrime s)).div ((angularG_hasDerivAt v θ u).differentiableAt.neg) (neg_ne_zero.mpr hg)

theorem microcore_mixed_identity (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im)
    (hg : angularG v θ u ≠ 0) (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    chartMixed s v θ u = chartSpatialB s v θ u*chartA s v θ u+
      chartB s v θ u*deriv (chartA s v θ) u := by
  have hprod := (chartB_angular s v θ u hr hi hn).mul (chartA_differentiableAt s v θ u hg).hasDerivAt
  have hneq : ∀ᶠ z in 𝓝 u, angularG v θ z ≠ 0 :=
    (angularG_hasDerivAt v θ u).continuousAt.eventually_ne hg
  have he : (fun z => chartB s v θ z*chartA s v θ z) =ᶠ[𝓝 u] chartTau s v θ := by
    filter_upwards [hneq] with z hz
    exact chartB_mul_chartA s v θ z hz
  have hprod' := hprod.congr_of_eventuallyEq he.symm
  exact (chartTau_angular s v θ u hr hi hn).unique hprod'

theorem microcoreField_hasFDerivAt {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (i : Fin (n+1)) (hg : angularG v θ (x i) ≠ 0) :
    HasFDerivAt (fun y => microcoreField v θ s y i)
      ((ContinuousLinearMap.proj (R := ℝ) i).smulRight (deriv (chartA s v θ) (x i))) x :=
  coordinate_hasFDerivAt _ _ x i (chartA_differentiableAt s v θ (x i) hg).hasDerivAt.comp_ofReal

theorem microcoreField_diagonal_derivative {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (i : Fin (n+1)) (hg : angularG v θ (x i) ≠ 0) :
    fderiv ℝ (fun y => microcoreField v θ s y i) x (Pi.single i 1)=
      deriv (chartA s v θ) (x i) := by
  rw [(microcoreField_hasFDerivAt v θ s x i hg).fderiv]
  simp

theorem microcore_jacobian_lie {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0) :
    lieStep (microcoreField v θ) (chartJacobian v θ) s x=0 := by
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x :=
    fun i => (microcoreField_hasFDerivAt v θ s x i (hg i)).differentiableAt
  rw [lieStep_eq_transport_sub _ _ s x hV (chartJacobian_spatial v θ s x hr hi hn).differentiableAt]
  unfold transport divergence
  rw [(chartJacobian_parameter v θ s x hs hr hi hn).deriv]
  simp_rw [chartJacobian_spatial_apply v θ s x hr hi hn,
    microcoreField_diagonal_derivative v θ s x _ (hg _)]
  rw [Finset.sum_mul]
  have he : ∀ i, deriv (chartA s v θ) (x i)*chartJacobian v θ s x =
      (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*
        (chartMixed s v θ (x i)-chartSpatialB s v θ (x i)*chartA s v θ (x i)) := by
    intro i
    have hp : chartJacobian v θ s x=
      (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*chartB s v θ (x i) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hp,microcore_mixed_identity s v θ (x i) (hr i) (hi i) (hg i) (hn i)]
    ring
  simp_rw [he]
  simp only [microcoreField,mul_sub,Finset.sum_sub_distrib]
  have hc : (∑ i, chartA s v θ (x i)*
      ((∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*chartSpatialB s v θ (x i))) =
      ∑ i, (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*
        (chartSpatialB s v θ (x i)*chartA s v θ (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring

/-- Source one-phase pullback identity, including the full chart Jacobian. -/
theorem microcore_pullback_lie {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    lieStep (microcoreField v θ) (chartPullback v θ F) s x =
      chartJacobian v θ s x*deriv (fun t => F t (chartMap v θ s x)) s := by
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x :=
    fun i => (microcoreField_hasFDerivAt v θ s x i (hg i)).differentiableAt
  have hFs : DifferentiableAt ℂ (fun t => F t (chartMap v θ t x)) s := by
    have hh := (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))).differentiableAt
    convert! hh using 1
  have hFx : DifferentiableAt ℝ (fun y => F s (chartMap v θ s y)) x := by
    have hh := ((hF.hasFDerivAt.restrictScalars ℝ).comp x
      ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))).differentiableAt
    convert! hh using 1
  have he : chartPullback v θ F=fun t y => F t (chartMap v θ t y)*chartJacobian v θ t y := by
    funext t y
    exact mul_comm _ _
  rw [he,lieStep_product_rule _ _ _ s x hFs
    (chartJacobian_parameter v θ s x hs hr hi hn).differentiableAt hFx
    (chartJacobian_spatial v θ s x hr hi hn).differentiableAt hV,
    microcore_jacobian_lie v θ s x hs hr hi hg hn,
    microcore_transport_chain v θ s x F hs hr hi hg hF]
  ring

end
end IsingBulk.Tail
