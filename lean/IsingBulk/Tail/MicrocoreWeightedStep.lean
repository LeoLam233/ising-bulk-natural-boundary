import IsingBulk.Tail.MicrocoreTopForm
import IsingBulk.Analysis.JetsTermPullback

/-! Weighted one-phase Lie recurrence. Every angular derivative remains on
its real cutoff, while analytic differentiation fixes every phase coordinate. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

 theorem microcore_pullback_differentiable {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    DifferentiableAt ℂ (fun t => chartPullback v θ F t x) s ∧
    DifferentiableAt ℝ (chartPullback v θ F s) x := by
  have hFs : DifferentiableAt ℂ (fun t => F t (chartMap v θ t x)) s := by
    have hh := (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (chartMap_parameter v θ s x hs hr hi))).differentiableAt
    convert! hh using 1
  have hFx : DifferentiableAt ℝ (fun y => F s (chartMap v θ s y)) x := by
    have hh := ((hF.hasFDerivAt.restrictScalars ℝ).comp x
      ((hasFDerivAt_const s x).prodMk (chartMap_spatial v θ s x hr hi))).differentiableAt
    convert! hh using 1
  exact ⟨(chartJacobian_parameter v θ s x hs hr hi hn).differentiableAt.mul hFs,
    (chartJacobian_spatial v θ s x hr hi hn).differentiableAt.mul hFx⟩

 theorem microcore_weighted_pullback_step {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (hw : DifferentiableAt ℝ w x) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re)
    (hn : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    lieStep (microcoreField v θ) (fun t y => (w y:ℂ)*chartPullback v θ F t y) s x =
      (w x:ℂ)*chartPullback v θ (fun t φ => deriv (fun z => F z φ) t) s x +
      ∑ i, (fderiv ℝ w x (Pi.single i 1):ℂ)*
        chartPullback v θ (fun t φ => -regularA t (φ i)*F t φ) s x := by
  have hgn : ∀ i, angularG v θ (x i) ≠ 0 := fun i hz => by simpa [hz] using hg i
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x :=
    fun i => (microcoreField_hasFDerivAt v θ s x i (hgn i)).differentiableAt
  obtain ⟨hFs,hFx⟩ := microcore_pullback_differentiable v θ s x F hs hr hi hn hF
  rw [lieStep_real_weight _ _ _ s x hw hFs hFx hV,
    microcore_pullback_lie v θ s x F hs hr hi hgn hn hF]
  simp only [chartPullback,regularA_chartPhase _ _ _ _ (hg _),microcoreField]
  rw [Finset.sum_mul]
  have he : (∑ i, chartA s v θ (x i)*(fderiv ℝ w x (Pi.single i 1):ℂ)*
      (chartJacobian v θ s x*F s (fun i => chartPhase s v θ (x i)))) =
      -∑ i, (fderiv ℝ w x (Pi.single i 1):ℂ)*
        (chartJacobian v θ s x*(-chartA s v θ (x i)*F s (fun i => chartPhase s v θ (x i)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  simp only [sub_neg_eq_add]
  congr 1

end
end IsingBulk.Tail
