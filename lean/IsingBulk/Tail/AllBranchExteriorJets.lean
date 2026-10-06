import IsingBulk.Analysis.JetsTheorem

/-! The actual selected-pair jet recurrence needs only a smooth real cutoff
on its open regular chart. This includes the source rational weights, which
are not globally smooth at full equality. FIRST machinery is unchanged. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

 theorem allBranchExterior_cutoffJet_contDiffAt {N : ℕ} (l : List (Fin N))
    (w : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (hw : ContDiffAt ℝ ∞ w x) :
    ContDiffAt ℝ ∞ (cutoffJet l w) x := by
  induction l with
  | nil => exact hw
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem allBranchExterior_source_step {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiffAt ℝ ∞ w x)
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
    ((allBranchExterior_cutoffJet_contDiffAt T.cutoff w x hw).differentiableAt (by simp))
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
theorem allBranchExterior_sourceValue_differentiable {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiffAt ℝ ∞ w x)
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
    ((allBranchExterior_cutoffJet_contDiffAt T.cutoff w x hw).differentiableAt (by simp)).hasFDerivAt
  constructor
  · convert! (differentiableAt_const (cutoffJet T.cutoff w x:ℂ)).mul
      (hJs.mul hFs.differentiableAt) using 1
  · convert! hwc.differentiableAt.mul (hJx.mul hFx.differentiableAt) using 1


theorem allBranchExterior_source_step_children {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (hpq : p ≠ q) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiffAt ℝ ∞ w x) (h : ActualJetPoint v θ p q s x)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x))
    (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (T.sourceValue p q v θ w Q) s x =
      ((actions (n+1)).map (fun a => (T.child p q a).sourceValue p q v θ w Q s x)).sum := by
  rw [allBranchExterior_source_step T v θ p q s x w Q hw hT hQ h.s_ne h.re_pos h.im_pos h.g_pos
    h.sin_ne h.b_ne h.slit h.delta_ne h.kernel_ne]
  have hb : regularB s (chartMap v θ s x p)-regularB s (chartMap v θ s x q) ≠ 0 := by
    simpa only [chartMap, regularB_chartPhase _ _ _ _ (h.g_pos _)] using h.b_ne
  rw [T.stepValue_eq_children p q hpq w Q x (s,chartMap v θ s x) hT hQ
    h.coefficient.regular_numerators.2 h.coefficient.continuity.1 h.coefficient.continuity.2
    h.s_ne h.slit h.y_den h.g_ne h.sin_ne hb h.delta_ne h.coefficient.gsum_ne
    h.coefficient.den_ne h.kernel_ne]
  simp_rw [SourceJetTerm.sourceValue_eq]
  rw [List.sum_map_mul_left]

theorem allBranchExterior_sourceTermSum_step {n : ℕ} (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ)
    (s : ℂ) (x : AngularSpace n) (hw : ContDiffAt ℝ ∞ w x)
    (h : ActualJetPoint v θ p q s x) (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (sourceTermSum p q v θ w Q j) s x =
      sourceTermSum p q v θ w Q (j+1) s x := by
  have hT := sourceJetTerms_analytic p q j (s,chartMap v θ s x)
    h.coefficient.regular_numerators.1 h.coefficient.regular_numerators.2
  have hdiff := fun T hmem => allBranchExterior_sourceValue_differentiable T v θ p q s x w Q hw
    (hT T hmem) hQ h.s_ne h.re_pos h.im_pos h.sin_ne h.slit h.delta_ne h.kernel_ne
  have hV := actualField_differentiable v θ p q s x h.re_pos h.im_pos
    (fun i hz => by simpa [hz] using h.g_pos i) h.sin_ne h.b_ne
  have he := lieStep_finite_sum (actualField v θ p q)
    ((sourceJetTerms p q j).map (fun T => T.sourceValue p q v θ w Q)) s x hV
    (by
      intro F hF
      obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hF
      exact (hdiff T hmem).1)
    (by
      intro F hF
      obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hF
      exact (hdiff T hmem).2)
  simp only [List.map_map, Function.comp_def] at he
  have heq := he.2.2
  change lieStep (actualField v θ p q) (sourceTermSum p q v θ w Q j) s x = _ at heq
  rw [heq]
  unfold sourceTermSum
  simp only [sourceJetTerms, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro T hmem
  exact allBranchExterior_source_step_children T v θ p q hpq s x w Q hw h (hT T hmem) hQ


theorem allBranchExterior_sourceJetTerms_all_order {n : ℕ} (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (A : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hw : ∀ x ∈ R, ContDiffAt ℝ ∞ w x)
    (hchart : ∀ s ∈ U, ∀ x ∈ R, ActualJetPoint v θ p q s x)
    (hA : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ A (s,chartMap v θ s x)) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (actualField v θ p q))^[j]
        (initialSourceDensity v θ w (unfactoredNumerator A))) s x =
      sourceTermSum p q v θ w (unfactoredNumerator A) j s x := by
  induction j with
  | zero =>
    intro s _ x _
    rw [sourceTermSum_zero]
    rfl
  | succ j ih =>
    intro s hs x hx
    rw [Function.iterate_succ_apply']
    rw [lieStep_congr_on (actualField v θ p q) hU hR ih hs hx]
    exact allBranchExterior_sourceTermSum_step p q hpq v θ w (unfactoredNumerator A) j s x (hw x hx) (hchart s hs x hx)
      (unfactoredNumerator_analytic A _ (hA s hs x hx))

end
end IsingBulk.Tail
