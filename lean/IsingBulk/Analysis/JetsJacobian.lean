import IsingBulk.Analysis.JetsCoefficientJets

/-! Source-specific mixed derivatives and the time derivative of the
diagonal chart Jacobian, needed by eq:pullbackLie. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Lie
open scoped BigOperators

def chartTau (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ :=
  -sourceSPrime s/Complex.sin (chartPhase s v θ u)

def chartMixed (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ :=
  angularG v θ u*sourceSPrime s*Complex.cos (chartPhase s v θ u)/
    (Complex.sin (chartPhase s v θ u))^3

theorem chartB_parameter (s : ℂ) (v θ : ℝ) (u : ℂ) (hs : s ≠ 0)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    HasDerivAt (fun t => chartB t v θ u) (chartMixed s v θ u) s := by
  have hh := (hasDerivAt_const s (angularG v θ u)).div
    (chartPhase_parameter s v θ u hs hr hi).csin hn
  convert! hh using 1
  unfold chartMixed
  field_simp
  ring

theorem chartTau_angular (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    HasDerivAt (chartTau s v θ) (chartMixed s v θ u) u := by
  have hh := (hasDerivAt_const u (-sourceSPrime s)).div
    (chartPhase_angular s v θ u hr hi).csin hn
  convert! hh using 1
  unfold chartMixed chartB
  field_simp
  ring

theorem chart_mixed_commute (s : ℂ) (v θ : ℝ) (u : ℂ) (hs : s ≠ 0)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    deriv (fun t => chartB t v θ u) s = deriv (chartTau s v θ) u := by
  rw [(chartB_parameter s v θ u hs hr hi hn).deriv,
    (chartTau_angular s v θ u hr hi hn).deriv]

def chartJacobian {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  ∏ i, chartB s v θ (x i)

def chartSpatialB (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ :=
  (-(angularY v θ u+(angularY v θ u)⁻¹)/2*Complex.sin (chartPhase s v θ u)-
    angularG v θ u*(Complex.cos (chartPhase s v θ u)*chartB s v θ u))/
      (Complex.sin (chartPhase s v θ u))^2

theorem angularG_hasDerivAt (v θ : ℝ) (u : ℂ) :
    HasDerivAt (angularG v θ) (-(angularY v θ u+(angularY v θ u)⁻¹)/2) u := by
  have hn : angularY v θ u ≠ 0 := Complex.exp_ne_zero _
  have hh := (((angularY_hasDerivAt v θ u).sub
    ((angularY_hasDerivAt v θ u).inv hn)).const_mul Complex.I).div_const 2
  convert! hh using 1
  field_simp
  simp [Complex.I_sq]

theorem chartB_angular (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    HasDerivAt (chartB s v θ) (chartSpatialB s v θ u) u := by
  exact (angularG_hasDerivAt v θ u).div (chartPhase_angular s v θ u hr hi).csin hn

theorem chartJacobian_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0) :
    HasFDerivAt (chartJacobian v θ s)
      (∑ i, (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k)) •
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) i).smulRight
          (chartSpatialB s v θ (x i)))) x := by
  have hh := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ =>
    coordinate_hasFDerivAt _ _ x i ((chartB_angular s v θ (x i) (hr i) (hi i) (hn i)).comp_ofReal))
  convert! hh using 1

theorem chartJacobian_spatial_apply {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0) (i : Fin (n+1)) :
    fderiv ℝ (chartJacobian v θ s) x (Pi.single i 1) =
      (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*chartSpatialB s v θ (x i) := by
  rw [(chartJacobian_spatial v θ s x hr hi hn).fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp [ite_smul, smul_eq_mul, mul_ite, Finset.sum_ite_eq']

theorem chartJacobian_parameter {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0) :
    HasDerivAt (fun t => chartJacobian v θ t x)
      (∑ i, (∏ k ∈ Finset.univ.erase i, chartB s v θ (x k))*chartMixed s v θ (x i)) s := by
  convert! HasDerivAt.fun_finsetProd
    (u := Finset.univ) (fun i _ => chartB_parameter s v θ (x i) hs (hr i) (hi i) (hn i)) using 1

def chartPullback {n : ℕ} (v θ : ℝ) (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (x : AngularSpace n) : ℂ :=
  chartJacobian v θ s x * F s (fun i => chartPhase s v θ (x i))

/-- The real cutoff part of eq:pullbackLie for the actual source chart.
The remaining unweighted Jacobian/divergence identity is kept separate. -/
theorem chartPullback_real_cutoff {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (w : AngularSpace n → ℝ) (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (x : AngularSpace n) (hw : DifferentiableAt ℝ w x)
    (hFs : DifferentiableAt ℂ (fun t => chartPullback v θ F t x) s)
    (hFx : DifferentiableAt ℝ (chartPullback v θ F s) x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => actualField v θ p q s y i) x) :
    lieStep (actualField v θ p q) (fun t y => (w y:ℂ)*chartPullback v θ F t y) s x =
      (w x:ℂ)*lieStep (actualField v θ p q) (chartPullback v θ F) s x -
      (∑ i, actualField v θ p q s x i*(fderiv ℝ w x (Pi.single i 1):ℂ))*
        chartPullback v θ F s x :=
  lieStep_real_weight _ w _ s x hw hFs hFx hV

end
end IsingBulk.Jets
