import IsingBulk.Tail.RightExteriorPairs

/-! Actual right-chart roots and annulus pole exclusion. The chart crosses
positive real exterior temperatures and overlaps the upper construction. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem annular_half_trace_norm {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ 1) : ‖(x+x⁻¹)/2‖ ≤ (1+r⁻¹)/2 := by
  have hi : ‖x⁻¹‖ ≤ r⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hr.trans_le hx) hr).mpr hx
  calc
    ‖(x+x⁻¹)/2‖ = ‖x+x⁻¹‖/2 := by rw [norm_div]; norm_num
    _ ≤ (1+r⁻¹)/2 := by have hh := norm_add_le x x⁻¹; linarith

theorem dispersion_re_positive_on_annulus {r : ℝ} (hr : 0 < r) {s x y : ℂ}
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) (hx1 : ‖x‖ ≤ 1) (hy1 : ‖y‖ ≤ 1)
    (hm : 1+r⁻¹ < (sourceS s).re) : 0 < (dispersion x y s).re := by
  have hX := (Complex.re_le_norm ((x+x⁻¹)/2)).trans (annular_half_trace_norm hr hx hx1)
  have hY := (Complex.re_le_norm ((y+y⁻¹)/2)).trans (annular_half_trace_norm hr hy hy1)
  simp only [dispersion, Complex.sub_re]
  linarith

theorem sourceW_right_of_margin {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re) (hy : ‖y‖=r) : 1 < (sourceW s y).re := by
  have hY := (Complex.re_le_norm ((y+y⁻¹)/2)).trans
    (annular_half_trace_norm hr (by rw [hy]) (by rw [hy]; exact hr1.le))
  have hi := (one_lt_inv₀ hr).mpr hr1
  simp only [sourceW, Complex.sub_re]
  linarith

def rightRoot (s y : ℂ) : ℂ := compactLeftRoot (sourceW s y)

theorem rightRoot_quadratic (s y : ℂ) :
    (rightRoot s y)^2-(2*sourceS s-y-y⁻¹)*rightRoot s y+1=0 := by
  have h := compactLeftRoot_quadratic (sourceW s y)
  dsimp only [rightRoot]
  unfold sourceW at *
  linear_combination h

theorem rightRoot_nonzero (s y : ℂ) : rightRoot s y ≠ 0 := compactLeftRoot_nonzero _

theorem rightRoot_dispersion (s y : ℂ) : dispersion (rightRoot s y) y s = 0 := by
  have ht := quadratic_root_trace (compactLeftRoot_quadratic (sourceW s y))
  change rightRoot s y+(rightRoot s y)⁻¹=2*sourceW s y at ht
  unfold dispersion sourceW at *
  linear_combination -ht/2

theorem rightRoot_inside_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re) (hy : ‖y‖=r) : ‖rightRoot s y‖ < r := by
  have hW := sourceW_right_of_margin hr hr1 hm hy
  have hn : ‖rightRoot s y‖ < 1 := compactLeftRoot_norm_lt_one hW
  by_contra hinside
  have hh := dispersion_re_positive_on_annulus hr (le_of_not_gt hinside) (by rw [hy])
    hn.le (by rw [hy]; exact hr1.le) hm
  rw [rightRoot_dispersion] at hh
  exact lt_irrefl (0:ℝ) hh

theorem rightRoot_admissible {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re) : ScalarResidueAdmissible r s (rightRoot s) :=
  ⟨hr,hr1,fun y _ => rightRoot_quadratic s y,
    fun _y hy => rightRoot_inside_radius hr hr1 hm hy⟩

theorem rightRoot_pair_norm {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y v : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re) (hy : ‖y‖=r) (hv : ‖v‖=r) :
    ‖pairKernel (rightRoot s y) (rightRoot s v)‖ ≤ 1 := by
  have hW := sourceW_right_of_margin hr hr1 hm hy
  have hV := sourceW_right_of_margin hr hr1 hm hv
  exact right_half_plane_root_pair_norm (compactLeftRoot_norm_lt_one hW)
    (compactLeftRoot_norm_lt_one hV) (compactLeftRoot_quadratic _) (compactLeftRoot_quadratic _) hW hV

theorem rightRoot_pairProduct_norm {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖=r) :
    ‖First.pairProduct (fun i => rightRoot s (y i))‖ ≤ 1 := by
  unfold First.pairProduct
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun j _ => rightRoot_pair_norm hr hr1 hm (hy i) (hy j))

end
end IsingBulk.Tail
