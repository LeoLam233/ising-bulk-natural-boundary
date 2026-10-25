import IsingBulk.Joint.FormFactors.ComplexRatioBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Local finite-order composition/product estimates in arbitrary complex
Banach parameter spaces. These apply to actual compact-integral coefficients,
without assuming a multivariable power-series presentation of the integral. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E H G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem contDiffAt_composition_geometric_jets {g : H → G} {f : E → H} {x : E}
    (j : ℕ) (hg : ContDiffAt ℂ j g (f x)) (hf : ContDiffAt ℂ j f x)
    {C D : ℝ} (hC : ∀ i ≤ j, ‖iteratedFDeriv ℂ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℂ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℂ j (g ∘ f) x‖ ≤ j.factorial*C*D^j := by
  obtain ⟨V,hVsub,hVo,hfx⟩ := _root_.eventually_nhds_iff.mp (hg.eventually (by simp))
  have he := (hf.eventually (by simp)).and (hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hfx))
  obtain ⟨U,hUsub,hUo,hx⟩ := _root_.eventually_nhds_iff.mp he
  have hgu : ContDiffOn ℂ j g V := fun y hy => (hVsub y hy).contDiffWithinAt
  have hfu : ContDiffOn ℂ j f U := fun y hy => (hUsub y hy).1.contDiffWithinAt
  have hh := norm_iteratedFDerivWithin_comp_le hgu hfu (n := j) le_rfl
    hVo.uniqueDiffOn hUo.uniqueDiffOn (fun y hy => (hUsub y hy).2) hx
    (C := C) (D := D)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hVo hfx] using hC)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hh

theorem contDiffAt_product_uniform_jets {f g : E → ℂ} {x : E} (J k : ℕ)
    (hk : k ≤ J) (hf : ContDiffAt ℂ J f x) (hg : ContDiffAt ℂ J g x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ J, ‖iteratedFDeriv ℂ i f x‖ ≤ C)
    (hgb : ∀ i ≤ J, ‖iteratedFDeriv ℂ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℂ k (fun y => f y*g y) x‖ ≤ 2^J*C*D := by
  obtain ⟨U,hU,hopen,hx⟩ := _root_.eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  have hfU : ContDiffOn ℂ J f U := fun y hy => (hU y hy).1.contDiffWithinAt
  have hgU : ContDiffOn ℂ J g U := fun y hy => (hU y hy).2.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_mul_le hfU hgU hopen.uniqueDiffOn hx (n := k) (by exact_mod_cast hk)
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hx] at hb
  calc
    _  ≤  ∑ i∈Finset.range (k+1), (k.choose i:ℝ)*‖iteratedFDeriv ℂ i f x‖*
        ‖iteratedFDeriv ℂ (k-i) g x‖ := hb
    _  ≤  ∑ i∈Finset.range (k+1), (k.choose i:ℝ)*C*D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ J := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      gcongr
      · exact hfb i hij
      · exact hgb (k-i) ((Nat.sub_le _ _).trans hk)
    _ = (2:ℝ)^k*C*D := by
      rw [←Finset.sum_mul,←Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _  ≤  _ := by gcongr; norm_num

/-- Finite derivative orders can all be bounded by one geometric constant,
uniformly over the compact set. -/
theorem compact_analytic_geometric_jets [CompleteSpace H] {f : Coupling → H}
    {K : Set Coupling} (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (j : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ q∈K, ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℂ i f q‖ ≤ D^i := by
  choose M hM hb using (fun i : ℕ => compact_analytic_all_jets_bound hK hf i)
  let D := 1+∑ i∈Finset.range (j+1), M i
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hM i).le))
  refine ⟨D,hD,?_⟩
  intro q hq i hi hij
  have hm := Finset.single_le_sum (fun a (_ : a∈Finset.range (j+1)) => (hM a).le)
    (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
  have hMD : M i ≤ D := by dsimp [D]; linarith
  exact (hb i q hq).trans (hMD.trans (by simpa using pow_le_pow_right₀ hD hi))

end
end IsingBulk.Joint.FormFactors
