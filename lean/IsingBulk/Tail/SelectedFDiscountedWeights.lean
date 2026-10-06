import IsingBulk.Tail.SelectedFActualOneBody
import IsingBulk.Tail.SelectedFActualPairs
import IsingBulk.Tail.SelectedWeightedPair
import IsingBulk.Tail.SelectedContourArithmetic
import IsingBulk.Analysis.BranchLength

/-! Actual one-angle discounted weights for the selected-F matching integral.
The compact Gaussian is absorbed pointwise before integration; the remaining
weight is independent of the coupled occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory Filter
open scoped BigOperators

 def discountedSelectedWeight (b η C eps L θ : ℝ) : ℝ :=
  if η^2/2 ≤ lowerChord b θ then C/L else C/Real.sqrt (|θ+b-2*Real.pi|+eps)

 theorem shifted_branch_weight_integral {C eps T a : ℝ}
    (hC : 0 ≤ C) (heps : 0 < eps) (hT : 0 ≤ T) (ha : 0 ≤ a) (haT : a ≤ T) :
    (∫ x in Icc 0 T, C/Real.sqrt (|x-a|+eps)) ≤ 4*C*Real.sqrt T := by
  let g : ℝ → ℝ := fun u => C/Real.sqrt (|u|+eps)
  have hg : Continuous g := continuous_const.div (continuous_abs.add continuous_const).sqrt
    (fun u => (Real.sqrt_pos.mpr (by positivity)).ne')
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT]
  change (∫ x in 0..T, g (x-a)) ≤ _
  rw [intervalIntegral.integral_comp_sub_right]
  apply (intervalIntegral.integral_mono_interval (c := -T) (d := T)
    (by linarith) (by linarith) (by linarith)
    (Filter.Eventually.of_forall (fun u => by dsimp [g]; positivity))
    (hg.intervalIntegrable (-T) T)).trans
  exact reciprocal_sqrt_integral eps T C heps hT hC

 theorem discountedSelectedWeight_integrable {b η C eps L : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hC : 0 ≤ C) (heps : 0 < eps) (hL : 1 ≤ L) :
    IntegrableOn (discountedSelectedWeight b η C eps L) (Icc 0 (2*Real.pi)) ∧
      (∀ θ, 0 ≤ discountedSelectedWeight b η C eps L θ) ∧
      (∀ θ, η^2/2 ≤ lowerChord b θ → discountedSelectedWeight b η C eps L θ=C/L) ∧
      (∫ θ in Icc 0 (2*Real.pi), discountedSelectedWeight b η C eps L θ) ≤
        4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi) := by
  classical
  let g : ℝ → ℝ := fun θ => C/Real.sqrt (|θ+b-2*Real.pi|+eps)
  let S : Set ℝ := {θ | η^2/2 ≤ lowerChord b θ}
  have hg : Continuous g := by
    have hc : Continuous (fun θ : ℝ => |θ+b-2*Real.pi|+eps) := by fun_prop
    exact continuous_const.div hc.sqrt (fun θ =>
      (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg _) heps)).ne')
  have hS : MeasurableSet S := (isClosed_le continuous_const (by unfold lowerChord; fun_prop)).measurableSet
  have hd : 0 ≤ C/L := div_nonneg hC (by linarith)
  obtain ⟨hi,hn,hbnd⟩ := discounted_vertex_integrable (by positivity : (0:ℝ)≤2*Real.pi) hd
    (hg.continuousOn.integrableOn_compact isCompact_Icc) (fun θ => by dsimp [g]; positivity) S hS
  have he : S.piecewise (fun _ => C/L) g=discountedSelectedWeight b η C eps L := by
    funext θ
    rfl
  rw [he] at hi hn hbnd
  refine ⟨hi,hn,?_,?_⟩
  · intro θ hθ
    simp [discountedSelectedWeight,hθ]
  · have hgi : (∫ θ in Icc 0 (2*Real.pi),g θ) ≤ 4*C*Real.sqrt (2*Real.pi) := by
      have he' : g=(fun θ => C/Real.sqrt (|θ-(2*Real.pi-b)|+eps)) := by
        funext θ
        dsimp [g]
        have hx : θ+b-2*Real.pi=θ-(2*Real.pi-b) := by ring
        rw [hx]
      rw [he']
      exact shifted_branch_weight_integral hC heps (by positivity) (by linarith) (by linarith)
    have hdisc : (C/L)*(2*Real.pi) ≤ C*(2*Real.pi) :=
      mul_le_mul_of_nonneg_right (div_le_self hC hL) (by positivity)
    linarith

 theorem discountedSelectedWeight_eq_product {b η C eps L θ : ℝ} :
    discountedSelectedWeight b η C eps L θ = selectedOneBodyBound b η C eps θ *
      (if η^2/2 ≤ lowerChord b θ then L⁻¹ else 1) := by
  by_cases hc : η^2/2 ≤ lowerChord b θ
  · simp only [discountedSelectedWeight,selectedOneBodyBound,ite_eq_left hc,ite_eq_right (not_lt.mpr hc)]
    exact div_eq_mul_inv _ _
  · simp [discountedSelectedWeight,selectedOneBodyBound,hc,lt_of_not_ge hc]

 theorem gaussian_selected_weight_product {N : ℕ} (b η C eps : ℝ) {a L : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hL : 0 < L) (θ : Fin N → ℝ) :
    Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2)*
      (∏ i, selectedOneBodyBound b η C eps (θ i)) ≤
      Real.exp ((Real.log L)^2/(4*a))*(∏ i, discountedSelectedWeight b η C eps L (θ i)) := by
  classical
  let M := (selectedCompactIndexSet b η θ).card
  have hgauss : Real.exp (-a*(M:ℝ)^2) ≤ Real.exp ((Real.log L)^2/(4*a))*(L⁻¹)^M := by
    rw [inv_pow,← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    simpa only [mul_comm] using compact_assignment_penalty (M := M) ha hL
  have hnon : 0 ≤ ∏ i, selectedOneBodyBound b η C eps (θ i) :=
    Finset.prod_nonneg (fun _ _ => selectedOneBodyBound_nonneg hC)
  have hprod : ∏ i, discountedSelectedWeight b η C eps L (θ i) =
      (∏ i, selectedOneBodyBound b η C eps (θ i))*(L⁻¹)^M := by
    simp_rw [discountedSelectedWeight_eq_product]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp [Finset.prod_ite,M,selectedCompactIndexSet]
  rw [hprod]
  exact (mul_le_mul_of_nonneg_right hgauss hnon).trans_eq (by ring)

end
end IsingBulk.Tail
