import IsingBulk.Analysis.JetsPoleCalculus

/-! Fixed local jets of the actual scalar regular factors. The bounds here
precede N because the functions have two or three variables. Propagating
these bounds through the full recurrence is a separate obligation. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch
open scoped BigOperators Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem regularPairCoefficient_joint_analytic (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularPairCoefficient z.1 z.2.1 z.2.2)
      (s,0,0) := by
  have hy := regularY_analytic_base s c hs hS hc
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularY z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularY z.1 z.2)
      (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hy (by fun_prop)
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularY z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularY z.1 z.2)
      (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hy (by fun_prop)
  have hsp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => halfSineQuotient (z.2.1+z.2.2)) (s,0,0) :=
    AnalyticAt.comp_of_eq halfSineQuotient_analytic (by fun_prop) (by simp)
  have hsm : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => halfSineQuotient (z.2.1-z.2.2)) (s,0,0) :=
    AnalyticAt.comp_of_eq halfSineQuotient_analytic (by fun_prop) (by simp)
  have hJ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => exponentialQuotient (z.2.1+z.2.2)) (s,0,0) :=
    AnalyticAt.comp_of_eq exponentialQuotient_analytic (by fun_prop) (by simp)
  have hden : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      1-(regularY z.1 z.2.1*regularY z.1 z.2.2)⁻¹) (s,0,0) :=
    analyticAt_const.sub ((hp.mul hq).inv (mul_ne_zero (regularY_ne_zero _ _) (regularY_ne_zero _ _)))
  have hH : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularDifferenceCoefficient z.1 z.2.1 z.2.2)
      (s,0,0) :=
    ((analyticAt_const.mul hsp).mul hsm).div hden (regularY_base_denominator s c hS hc)
  have hep : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => Complex.exp (-Complex.I*z.2.1)) (s,0,0) := by fun_prop
  have heq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => Complex.exp (-Complex.I*z.2.2)) (s,0,0) := by fun_prop
  exact (((hH.pow 2).neg.mul hep).mul heq).div ((hp.mul hq).mul (hJ.pow 2))
    (by simp [exponentialQuotient_zero, regularY_ne_zero])

theorem finite_analytic_jets_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ∀ k ≤ j, ‖iteratedFDeriv ℂ k f y‖ ≤ C := by
  let C : ℝ := 1+∑ k ∈ Finset.range (j+1), ‖iteratedFDeriv ℂ k f x‖
  have hpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hpos,?_⟩
  have he : ∀ k ∈ Finset.range (j+1), ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv ℂ k f y‖ ≤ C := by
    intro k hk
    have hb : ‖iteratedFDeriv ℂ k f x‖ < C := by
      have hm := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) =>
        norm_nonneg (iteratedFDeriv ℂ l f x)) hk
      dsimp [C]
      linarith
    have hcont : ContinuousAt (fun y => ‖iteratedFDeriv ℂ k f y‖) x :=
      (hf.contDiffAt.continuousAt_iteratedFDeriv (n := ⊤) (by simp)).norm
    exact (hcont.eventually_lt continuousAt_const hb).mono fun _ h => h.le
  filter_upwards [((Finset.range (j+1)).eventually_all).mpr he] with y hy
  intro k hk
  exact hy k (Finset.mem_range.mpr (by omega))

/-- Joint s/phi jets, with the neighborhood and constant chosen independently
of N. This is the scalar input bound, not the generated-coefficient bound. -/
theorem source_scalar_jets_bounded (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (j : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (s,0), ∀ k ≤ j,
      ‖iteratedFDeriv ℂ k (fun t : ℂ × ℂ => regularA t.1 t.2) z‖ ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (s,0,0), ∀ k ≤ j,
      ‖iteratedFDeriv ℂ k (fun t : ℂ × ℂ × ℂ => selectedRegularFactor t.1 t.2.1 t.2.2) z‖ ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (s,0,0), ∀ k ≤ j,
      ‖iteratedFDeriv ℂ k (fun t : ℂ × ℂ × ℂ => regularPairCoefficient t.1 t.2.1 t.2.2) z‖ ≤ C) := by
  exact ⟨finite_analytic_jets_bounded _ _ (regularA_analytic_base s c hs hS hc) j,
    finite_analytic_jets_bounded _ _ (selectedRegularFactor_analytic_base s c hs hS hc) j,
    finite_analytic_jets_bounded _ _ (regularPairCoefficient_joint_analytic s c hs hS hc) j⟩

end
end IsingBulk.Jets
