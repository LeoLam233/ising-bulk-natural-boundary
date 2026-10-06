import IsingBulk.Analysis.JetsTermStep

/-! Pullback realization of an individual semantic term. All derivatives of
the cutoff remain on its real domain. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch IsingBulk.Lie
open scoped ContDiff
attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem regularKernel_analytic {N : ℕ} (z : ℂ × (Fin N → ℂ)) (hs : z.1 ≠ 0)
    (hslit : ∀ i, 1-(z.1+z.1⁻¹-Complex.cos (z.2 i))^2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularKernel t.1 t.2) z := by
  have hY : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularYProduct t.1 t.2) z := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (g := fun t : ℂ × ℂ => regularY t.1 t.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i))
      (regularY_analytic z.1 (z.2 i) hs (hslit i))
      (analyticAt_fst.prod (analytic_coordinate i z))
  have hZ : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularZProduct t.1 t.2) z := by
    unfold regularZProduct
    have ha : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) =>
        -Complex.I * ∑ i, t.2 i) z :=
      analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => analytic_coordinate i z)
    exact ha.cexp
  exact (analyticAt_const.sub hY).mul (analyticAt_const.sub hZ)

theorem cutoffJet_contDiff {N : ℕ} (l : List (Fin N)) (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (cutoffJet l w) := by
  induction l with
  | nil => exact hw
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

def SourceJetTerm.sourceValue {n : ℕ} (T : SourceJetTerm (n+1)) (p q : Fin (n+1))
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (x : AngularSpace n) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ) * chartPullback v θ (T.density p q Q) s x

theorem SourceJetTerm.sourceValue_eq {n : ℕ} (T : SourceJetTerm (n+1)) (p q : Fin (n+1))
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (x : AngularSpace n) :
    T.sourceValue p q v θ w Q s x = chartJacobian v θ s x *
      T.value p q w Q x (s,chartMap v θ s x) := by
  unfold SourceJetTerm.sourceValue SourceJetTerm.value chartPullback chartMap
  ring

theorem SourceJetTerm.source_step {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiff ℝ ∞ w)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x))
    (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hb : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0)
    (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (chartPhase s v θ (x i)))^2 ∈ Complex.slitPlane)
    (hd : chartMap v θ s x q-chartMap v θ s x p ≠ 0)
    (hK : regularKernel s (chartMap v θ s x) ≠ 0) :
    lieStep (actualField v θ p q) (T.sourceValue p q v θ w Q) s x =
      chartJacobian v θ s x * T.stepValue p q w Q x (s,chartMap v θ s x) := by
  have hC : AnalyticAt ℂ (T.coefficient p q) (s,chartMap v θ s x) :=
    hT.div (((selectedDifferenceCLM p q).analyticAt _).pow T.pole) (pow_ne_zero T.pole hd)
  have hJ := directionJet_analytic numeratorDirection T.numerator Q _ hQ
  have hF := (hC.mul hJ).div (regularKernel_analytic _ hs hslit) hK
  have he := pullbackLie_selected v θ p q s x (cutoffJet T.cutoff w) (T.density p q Q)
    hs hr hi hg hn hb hslit hF.differentiableAt
    ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) x)
  change lieStep (actualField v θ p q) (T.sourceValue p q v θ w Q) s x = _ at he
  rw [he, SourceJetTerm.stepValue]
  have hv := regularSelectedField_chart p q v θ s x hg
  change regularSelectedField p q s (chartMap v θ s x) = _ at hv
  rw [hv]
  simp only [cutoffJet, chartPullback]
  ring_nf
  rfl

/-- The regularity required by finite-sum linearity follows from the actual
chart and analytic coefficient/numerator germs and the real smooth cutoff. -/
theorem SourceJetTerm.sourceValue_differentiable {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiff ℝ ∞ w)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x))
    (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (chartPhase s v θ (x i)))^2 ∈ Complex.slitPlane)
    (hd : chartMap v θ s x q-chartMap v θ s x p ≠ 0)
    (hK : regularKernel s (chartMap v θ s x) ≠ 0) :
    DifferentiableAt ℂ (fun t => T.sourceValue p q v θ w Q t x) s ∧
      DifferentiableAt ℝ (T.sourceValue p q v θ w Q s) x := by
  have hC : AnalyticAt ℂ (T.coefficient p q) (s,chartMap v θ s x) :=
    hT.div (((selectedDifferenceCLM p q).analyticAt _).pow T.pole) (pow_ne_zero T.pole hd)
  have hJ := directionJet_analytic numeratorDirection T.numerator Q _ hQ
  have hF := (hC.mul hJ).div (regularKernel_analytic _ hs hslit) hK
  have hFs := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))
  have hFx := (hF.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x
    ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))
  have hJs := (chartJacobian_parameter v θ s x hs hr hi hn).differentiableAt
  have hJx := (chartJacobian_spatial v θ s x hr hi hn).differentiableAt
  have hwc := Complex.ofRealCLM.hasFDerivAt.comp x
    ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) x).hasFDerivAt
  constructor
  · convert! (differentiableAt_const (cutoffJet T.cutoff w x:ℂ)).mul
      (hJs.mul hFs.differentiableAt) using 1
  · convert! hwc.differentiableAt.mul (hJx.mul hFx.differentiableAt) using 1

end
end IsingBulk.Jets
