import IsingBulk.Analysis.JetsLocalChart

/-! Local all-order equality for the existing semantic list. The induction
uses equality on open parameter/angular sets before taking each derivative. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Lie
open scoped ContDiff

theorem SourceJetTerm.source_step_children {n : ℕ} (T : SourceJetTerm (n+1))
    (v θ : ℝ) (p q : Fin (n+1)) (hpq : p ≠ q) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (h : ActualJetPoint v θ p q s x)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v θ s x))
    (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (T.sourceValue p q v θ w Q) s x =
      ((actions (n+1)).map (fun a => (T.child p q a).sourceValue p q v θ w Q s x)).sum := by
  rw [T.source_step v θ p q s x w Q hw hT hQ h.s_ne h.re_pos h.im_pos h.g_pos
    h.sin_ne h.b_ne h.slit h.delta_ne h.kernel_ne]
  have hb : regularB s (chartMap v θ s x p)-regularB s (chartMap v θ s x q) ≠ 0 := by
    simpa only [chartMap, regularB_chartPhase _ _ _ _ (h.g_pos _)] using h.b_ne
  rw [T.stepValue_eq_children p q hpq w Q x (s,chartMap v θ s x) hT hQ
    h.coefficient.regular_numerators.2 h.coefficient.continuity.1 h.coefficient.continuity.2
    h.s_ne h.slit h.y_den h.g_ne h.sin_ne hb h.delta_ne h.coefficient.gsum_ne
    h.coefficient.den_ne h.kernel_ne]
  simp_rw [SourceJetTerm.sourceValue_eq]
  rw [List.sum_map_mul_left]

def initialSourceDensity {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  (w x:ℂ)*chartPullback v θ (fun t φ => Q (t,φ)/regularKernel t φ) s x

def sourceTermSum {n : ℕ} (p q : Fin (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (j : ℕ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  ((sourceJetTerms p q j).map (fun T => T.sourceValue p q v θ w Q s x)).sum

theorem sourceTermSum_zero {n : ℕ} (p q : Fin (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) :
    sourceTermSum p q v θ w Q 0 = initialSourceDensity v θ w Q := by
  funext s x
  simp [sourceTermSum, sourceJetTerms, SourceJetTerm.sourceValue, SourceJetTerm.density,
    SourceJetTerm.coefficient, numeratorJet, directionJet, cutoffJet, initialSourceDensity,
    chartPullback]

theorem sourceTermSum_step {n : ℕ} (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ)
    (s : ℂ) (x : AngularSpace n) (hw : ContDiff ℝ ∞ w)
    (h : ActualJetPoint v θ p q s x) (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) :
    lieStep (actualField v θ p q) (sourceTermSum p q v θ w Q j) s x =
      sourceTermSum p q v θ w Q (j+1) s x := by
  have hT := sourceJetTerms_analytic p q j (s,chartMap v θ s x)
    h.coefficient.regular_numerators.1 h.coefficient.regular_numerators.2
  have hdiff := fun T hmem => SourceJetTerm.sourceValue_differentiable T v θ p q s x w Q hw
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
  exact T.source_step_children v θ p q hpq s x w Q hw h (hT T hmem) hQ

/-- The entire previous density stays under lieStep. The open-set induction
hypothesis is used via lieStep_congr_on, never as a bare pointwise rewrite. -/
theorem sourceJetTerms_all_order {n : ℕ} (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (A : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hw : ContDiff ℝ ∞ w)
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
    exact sourceTermSum_step p q hpq v θ w (unfactoredNumerator A) j s x hw (hchart s hs x hx)
      (unfactoredNumerator_analytic A _ (hA s hs x hx))

end
end IsingBulk.Jets
