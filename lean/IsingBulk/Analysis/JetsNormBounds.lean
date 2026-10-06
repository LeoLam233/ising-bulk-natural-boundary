import IsingBulk.Analysis.JetsTerms
import IsingBulk.Analysis.JetsCoefficientJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Local finite-jet norm estimates for the coefficient recurrence. Constants
in these calculus inequalities do not depend on the dimension of the domain. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_product_jet_bound (f g : E → ℂ) (x : E) (k : ℕ)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    ‖iteratedFDeriv ℂ k (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*‖iteratedFDeriv ℂ i f x‖*
        ‖iteratedFDeriv ℂ (k-i) g x‖ := by
  obtain ⟨U,hU,hopen,hx⟩ := eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hfU : ContDiffOn ℂ ω f U := fun y hy => (hU y hy).1.contDiffAt.contDiffWithinAt
  have hgU : ContDiffOn ℂ ω g U := fun y hy => (hU y hy).2.contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_mul_le hfU hgU hopen.uniqueDiffOn hx (n := k) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

theorem analytic_product_uniform_jet_bound (f g : E → ℂ) (x : E) (J k : ℕ)
    (hk : k ≤ J) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ J, ‖iteratedFDeriv ℂ i f x‖ ≤ C)
    (hgb : ∀ i ≤ J, ‖iteratedFDeriv ℂ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℂ k (fun y => f y*g y) x‖ ≤ 2^J*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*‖iteratedFDeriv ℂ i f x‖*
        ‖iteratedFDeriv ℂ (k-i) g x‖ := analytic_product_jet_bound f g x k hf hg
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*C*D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ J := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      gcongr
      · exact hfb i hij
      · exact hgb (k-i) ((Nat.sub_le _ _).trans hk)
    _ = (2:ℝ)^k*C*D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ _ := by gcongr; norm_num

theorem analytic_direction_jet_bound (f : E → ℂ) (x e : E) (k : ℕ)
    (hf : AnalyticAt ℂ f x) :
    ‖iteratedFDeriv ℂ k (fun y => fderiv ℂ f y e) x‖ ≤
      ‖e‖*‖iteratedFDeriv ℂ (k+1) f x‖ := by
  have hb := norm_iteratedFDeriv_clm_apply_const (c := e) (n := k) (N := ⊤)
    hf.fderiv.contDiffAt (by simp)
  rwa [norm_iteratedFDeriv_fderiv] at hb

theorem analytic_linear_comp_jet_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : F → ℂ) (L : E →L[ℂ] F) (x : E) (k : ℕ)
    (hf : AnalyticAt ℂ f (L x)) (hL : ‖L‖ ≤ 1) :
    ‖iteratedFDeriv ℂ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℂ k f (L x)‖ := by
  obtain ⟨U,hU,hopen,hx⟩ := eventually_nhds_iff.mp hf.eventually_analyticAt
  have hfU : ContDiffOn ℂ ω f U := fun y hy => (hU y hy).contDiffAt.contDiffWithinAt
  have hop : IsOpen (L ⁻¹' U) := hopen.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfU hopen.uniqueDiffOn hop.uniqueDiffOn hx
    (i := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hop hx,
    iteratedFDerivWithin_of_isOpen _ hopen hx] at he
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

def scalarCoordinate {N : ℕ} (i : Fin N) : (ℂ × (Fin N → ℂ)) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
    ((ContinuousLinearMap.proj (R := ℂ) i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))

theorem scalarCoordinate_norm {N : ℕ} (i : Fin N) : ‖scalarCoordinate i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖(z.1,z.2 i)‖ ≤ 1*‖z‖
  simp only [one_mul, Prod.norm_def]
  exact max_le (le_max_left _ _) ((norm_le_pi_norm z.2 i).trans (le_max_right _ _))

/-- The scalar a_i jets lift to arbitrary dimension with no loss, and the
actual aSum contributes exactly the permitted linear factor N. -/
theorem aSum_jet_bound {N : ℕ} (z : ℂ × (Fin N → ℂ)) (k : ℕ) (C : ℝ)
    (ha : ∀ i, AnalyticAt ℂ (fun t : ℂ × ℂ => regularA t.1 t.2) (z.1,z.2 i))
    (hb : ∀ i, ‖iteratedFDeriv ℂ k (fun t : ℂ × ℂ => regularA t.1 t.2) (z.1,z.2 i)‖ ≤ C) :
    ‖iteratedFDeriv ℂ k (fun t : ℂ × (Fin N → ℂ) => aSum t.1 t.2) z‖ ≤ N*C := by
  have hc : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) z := by
    intro i
    exact AnalyticAt.comp (g := fun t : ℂ × ℂ => regularA t.1 t.2)
      (f := scalarCoordinate i) (ha i) ((scalarCoordinate i).analyticAt z)
  unfold aSum
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hc i).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin N, C := by
      apply Finset.sum_le_sum
      intro i _
      exact (analytic_linear_comp_jet_bound _ (scalarCoordinate i) z k (ha i)
        (scalarCoordinate_norm i)).trans (hb i)
    _ = _ := by simp

/-- Fixed scalar neighborhood and constant are chosen before N. This is
the actual sum in eq:twofield, rather than an N-dimensional compactness bound. -/
theorem aSum_uniform_jets (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (s,0) ∈ U ∧
      ∀ N : ℕ, ∀ z : ℂ × (Fin N → ℂ), (∀ i, (z.1,z.2 i) ∈ U) → ∀ k ≤ j,
        ‖iteratedFDeriv ℂ k (fun t : ℂ × (Fin N → ℂ) => aSum t.1 t.2) z‖ ≤ N*C := by
  have ha := regularA_analytic_base s c hs hS hc
  obtain ⟨C,hC,hb⟩ := finite_analytic_jets_bounded _ _ ha j
  obtain ⟨U,hU,ho,hx⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and hb)
  refine ⟨C,hC,U,ho,hx,?_⟩
  intro N z hz k hk
  exact aSum_jet_bound z k C (fun i => (hU _ (hz i)).1)
    (fun i => (hU _ (hz i)).2 k hk)

end
end IsingBulk.Jets
