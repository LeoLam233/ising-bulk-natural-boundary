import IsingBulk.Analysis.JetsNormBounds

/-! Finite derivative budgets for the six actual coefficient updates. -/
namespace IsingBulk.Jets
noncomputable section
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

structure JetBound (f : E → ℂ) (z : E) (J : ℕ) (C : ℝ) : Prop where
  analytic : AnalyticAt ℂ f z
  nonneg : 0 ≤ C
  bound : ∀ k ≤ J, ‖iteratedFDeriv ℂ k f z‖ ≤ C

theorem JetBound.mono {f : E → ℂ} {z : E} {J K : ℕ} {C D : ℝ}
    (h : JetBound f z J C) (hK : K ≤ J) (hD : C ≤ D) : JetBound f z K D :=
  ⟨h.analytic,h.nonneg.trans hD,fun k hk => (h.bound k (hk.trans hK)).trans hD⟩

theorem JetBound.const (c : ℂ) (z : E) (J : ℕ) :
    JetBound (fun _ : E => c) z J ‖c‖ := by
  refine ⟨analyticAt_const,norm_nonneg _,?_⟩
  intro k _
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]

theorem JetBound.add {f g : E → ℂ} {z : E} {J : ℕ} {C D : ℝ}
    (hf : JetBound f z J C) (hg : JetBound g z J D) :
    JetBound (fun y => f y+g y) z J (C+D) := by
  refine ⟨hf.analytic.add hg.analytic,add_nonneg hf.nonneg hg.nonneg,?_⟩
  intro k hk
  change ‖iteratedFDeriv ℂ k (f+g) z‖ ≤ C+D
  rw [iteratedFDeriv_add_apply hf.analytic.contDiffAt hg.analytic.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound k hk) (hg.bound k hk))

theorem JetBound.neg {f : E → ℂ} {z : E} {J : ℕ} {C : ℝ}
    (h : JetBound f z J C) : JetBound (fun y => -f y) z J C := by
  refine ⟨h.analytic.neg,h.nonneg,?_⟩
  intro k hk
  change ‖iteratedFDeriv ℂ k (-f) z‖ ≤ C
  simpa only [iteratedFDeriv_neg_apply,norm_neg] using h.bound k hk

theorem JetBound.sub {f g : E → ℂ} {z : E} {J : ℕ} {C D : ℝ}
    (hf : JetBound f z J C) (hg : JetBound g z J D) :
    JetBound (fun y => f y-g y) z J (C+D) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem JetBound.mul {f g : E → ℂ} {z : E} {J : ℕ} {C D : ℝ}
    (hf : JetBound f z J C) (hg : JetBound g z J D) :
    JetBound (fun y => f y*g y) z J (2^J*C*D) :=
  ⟨hf.analytic.mul hg.analytic,mul_nonneg (mul_nonneg (by positivity) hf.nonneg) hg.nonneg,fun k hk =>
    analytic_product_uniform_jet_bound f g z J k hk hf.analytic hg.analytic C D
      hf.nonneg hg.nonneg hf.bound hg.bound⟩

theorem JetBound.direction {f : E → ℂ} {z : E} {J : ℕ} {C : ℝ}
    (h : JetBound f z (J+1) C) (e : E) (he : ‖e‖ ≤ 1) :
    JetBound (fun y => fderiv ℂ f y e) z J C := by
  refine ⟨((ContinuousLinearMap.apply ℂ ℂ e).analyticAt _).comp h.analytic.fderiv,h.nonneg,?_⟩
  intro k hk
  exact (analytic_direction_jet_bound f z e k h.analytic).trans
    ((mul_le_mul_of_nonneg_left (h.bound (k+1) (by omega)) (norm_nonneg _)).trans
      (mul_le_of_le_one_left h.nonneg he))

theorem JetBound.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : F → ℂ} {z : E} {J : ℕ} {C : ℝ} (L : E →L[ℂ] F)
    (h : JetBound f (L z) J C) (hL : ‖L‖ ≤ 1) : JetBound (f ∘ L) z J C :=
  ⟨h.analytic.comp (L.analyticAt z),h.nonneg,fun k hk =>
    (analytic_linear_comp_jet_bound f L z k h.analytic hL).trans (h.bound k hk)⟩

theorem JetBound.sum {N : ℕ} {f : Fin N → E → ℂ} {z : E} {J : ℕ} {C : ℝ}
    (h : ∀ i, JetBound (f i) z J C) (hC : 0 ≤ C) :
    JetBound (fun y => ∑ i, f i y) z J (N*C) := by
  refine ⟨Finset.analyticAt_fun_sum _ (fun i _ => (h i).analytic),by positivity,?_⟩
  intro k hk
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (h i).analytic.contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => (h i).bound k hk)
    _ = _ := by simp

theorem JetBound.ite {f : E → ℂ} {z : E} {J : ℕ} {C : ℝ}
    (h : JetBound f z J C) (P : Prop) [Decidable P] :
    JetBound (fun y => if P then f y else 0) z J C := by
  split_ifs
  · exact h
  · exact (JetBound.const 0 z J).mono le_rfl (by simpa using h.nonneg)

theorem spatialDirection_norm_le {N : ℕ} (i : Fin N) : ‖spatialDirection i‖ ≤ 1 := by
  simp [spatialDirection,Prod.norm_def,Pi.norm_single]

theorem parameterDirection_norm_le {N : ℕ} : ‖((1:ℂ),(0:Fin N → ℂ))‖ ≤ 1 := by simp

theorem selectedDifference_direction_bound {N : ℕ} (p q i : Fin N) :
    ‖selectedDifferenceCLM p q (spatialDirection i)‖ ≤ 2 := by
  change ‖(Pi.single (M := fun _ : Fin N => ℂ) i 1) q-
    (Pi.single (M := fun _ : Fin N => ℂ) i 1) p‖ ≤ 2
  have hp : ‖(Pi.single (M := fun _ : Fin N => ℂ) i 1) p‖ ≤ 1 := by
    simp only [Pi.single_apply]; split_ifs <;> norm_num
  have hq : ‖(Pi.single (M := fun _ : Fin N => ℂ) i 1) q‖ ≤ 1 := by
    simp only [Pi.single_apply]; split_ifs <;> norm_num
  exact (norm_sub_le _ _).trans (by linarith)

end
end IsingBulk.Jets
