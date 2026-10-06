import IsingBulk.Tail.MicrocoreJetTerms
import IsingBulk.Analysis.JetsAllOrder

/-! All-order local equality for the actual microcore field. Each induction
step uses equality on an open set before taking further derivatives. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

structure MicrocoreJetPoint {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) : Prop where
  s_ne : s ≠ 0
  re_pos : ∀ i, 0 < (chartW s v θ (x i)).re
  im_pos : ∀ i, 0 < (chartW s v θ (x i)).im
  g_pos : ∀ i, 0 < (angularG v θ (x i)).re
  sin_ne : ∀ i, Complex.sin (chartPhase s v θ (x i)) ≠ 0
  slit : ∀ i, 1-(s+s⁻¹-Complex.cos (chartPhase s v θ (x i)))^2 ∈ Complex.slitPlane

theorem MicrocoreJetPoint.regularA_analytic {n : ℕ} {v θ : ℝ} {s : ℂ} {x : AngularSpace n}
    (h : MicrocoreJetPoint v θ s x) (i : Fin (n+1)) :
    AnalyticAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => regularA z.1 (z.2 i))
      (s,chartMap v θ s x) := by
  have hy := AnalyticAt.comp (g := fun z : ℂ × ℂ => IsingBulk.Branch.regularY z.1 z.2)
    (f := fun z : ℂ × (Fin (n+1) → ℂ) => (z.1,z.2 i))
    (x := (s,chartMap v θ s x))
    (IsingBulk.Branch.regularY_analytic s _ h.s_ne (h.slit i))
    (analyticAt_fst.prod (analytic_coordinate i _))
  have hG : AnalyticAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => regularG z.1 (z.2 i))
      (s,chartMap v θ s x) :=
    (analyticAt_const.mul (hy.sub (hy.inv (IsingBulk.Branch.regularY_ne_zero s _)))).div_const
  have hg : regularG s (chartMap v θ s x i) ≠ 0 := by
    rw [chartMap,regularG_chartPhase _ _ _ _ (h.g_pos i)]
    intro hz
    simpa [hz] using h.g_pos i
  exact (analyticAt_const.sub ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 h.s_ne))).div
    hG.neg (neg_ne_zero.mpr hg)

def microcoreTermSum {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  ((microcoreJetTerms F j).map (fun T => T.sourceValue v θ w s x)).sum

theorem microcoreTermSum_step {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (x : AngularSpace n)
    (hw : ContDiff ℝ ∞ w) (h : MicrocoreJetPoint v θ s x)
    (hF : AnalyticAt ℂ F (s,chartMap v θ s x)) :
    lieStep (microcoreField v θ) (microcoreTermSum v θ w F j) s x =
      microcoreTermSum v θ w F (j+1) s x := by
  have hT := microcoreJetTerms_analytic F j (s,chartMap v θ s x) hF h.regularA_analytic
  have hd := fun T hmem => MicrocoreJetTerm.source_differentiable T v θ s x w hw h.s_ne
    h.re_pos h.im_pos h.sin_ne (hT T hmem)
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x := by
    intro i
    apply (microcoreField_hasFDerivAt v θ s x i _).differentiableAt
    intro hz
    simpa [hz] using h.g_pos i
  have he := lieStep_finite_sum (microcoreField v θ)
    ((microcoreJetTerms F j).map (fun T => T.sourceValue v θ w)) s x hV
    (by intro G hG; obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hG; exact (hd T hmem).1)
    (by intro G hG; obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hG; exact (hd T hmem).2)
  simp only [List.map_map,Function.comp_def] at he
  have heq := he.2.2
  change lieStep (microcoreField v θ) (microcoreTermSum v θ w F j) s x=_ at heq
  rw [heq]
  unfold microcoreTermSum
  simp only [microcoreJetTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,
    List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro T hmem
  exact T.source_step v θ s x w hw h.s_ne h.re_pos h.im_pos h.g_pos h.sin_ne (hT T hmem)

theorem microcoreJetTerms_all_order {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (U : Set ℂ) (R : Set (AngularSpace n))
    (hU : IsOpen U) (hR : IsOpen R) (hw : ContDiff ℝ ∞ w)
    (hchart : ∀ s ∈ U, ∀ x ∈ R, MicrocoreJetPoint v θ s x)
    (hF : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ F (s,chartMap v θ s x)) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (microcoreField v θ))^[j]
        (fun t y => (w y:ℂ)*chartPullback v θ (fun t φ => F (t,φ)) t y)) s x =
      microcoreTermSum v θ w F j s x := by
  induction j with
  | zero => intro s _ x _; simp [microcoreTermSum,microcoreJetTerms,MicrocoreJetTerm.sourceValue,cutoffJet]
  | succ j ih =>
    intro s hs x hx
    rw [Function.iterate_succ_apply']
    rw [lieStep_congr_on (microcoreField v θ) hU hR ih hs hx]
    exact microcoreTermSum_step v θ w F j s x hw (hchart s hs x hx) (hF s hs x hx)

end
end IsingBulk.Tail
