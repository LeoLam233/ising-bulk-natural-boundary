import IsingBulk.Tail.RightExteriorRoots
import IsingBulk.Tail.RightReducedMajorant
import IsingBulk.Tail.ExteriorFormFactors

/-! Genuine left-chart roots and pole exclusion for the original offsite
integral. Odd offsite coefficients are never replaced by right coefficients
at the negative argument. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set
open scoped BigOperators

def leftRoot (s y : ℂ) : ℂ := -rightRoot (-s) (-y)

theorem left_dispersion_re_negative_on_annulus {r : ℝ} (hr : 0 < r) {x y s : ℂ}
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) (hx1 : ‖x‖ ≤ 1) (hy1 : ‖y‖ ≤ 1)
    (hm : 1+r⁻¹ < -(sourceS s).re) : (dispersion x y s).re < 0 := by
  have hn : 1+r⁻¹ < (sourceS (-s)).re := by simpa only [sourceS_neg,Complex.neg_re] using hm
  have hh := dispersion_re_positive_on_annulus hr
    (x := -x) (y := -y) (by simpa using hx) (by simpa using hy)
    (by simpa using hx1) (by simpa using hy1) hn
  simpa only [dispersion_neg,Complex.neg_re,neg_pos] using hh

theorem leftRoot_quadratic (s y : ℂ) :
    (leftRoot s y)^2-(2*sourceS s-y-y⁻¹)*leftRoot s y+1=0 := by
  have hh := rightRoot_quadratic (-s) (-y)
  simp only [sourceS_neg,inv_neg] at hh
  dsimp only [leftRoot]
  linear_combination hh

theorem leftRoot_inside_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y : ℂ}
    (hm : 1+r⁻¹ < -(sourceS s).re) (hy : ‖y‖=r) : ‖leftRoot s y‖ < r := by
  have hn : 1+r⁻¹ < (sourceS (-s)).re := by simpa only [sourceS_neg,Complex.neg_re] using hm
  simpa only [leftRoot,norm_neg] using rightRoot_inside_radius hr hr1 hn
    (y := -y) (by simpa only [norm_neg] using hy)

theorem leftRoot_admissible {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : 1+r⁻¹ < -(sourceS s).re) : ScalarResidueAdmissible r s (leftRoot s) :=
  ⟨hr,hr1,fun y _ => leftRoot_quadratic s y,
    fun _y hy => leftRoot_inside_radius hr hr1 hm hy⟩

theorem leftRoot_pair_norm {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y v : ℂ}
    (hm : 1+r⁻¹ < -(sourceS s).re) (hy : ‖y‖=r) (hv : ‖v‖=r) :
    ‖pairKernel (leftRoot s y) (leftRoot s v)‖ ≤ 1 := by
  have hn : 1+r⁻¹ < (sourceS (-s)).re := by simpa only [sourceS_neg,Complex.neg_re] using hm
  simpa only [leftRoot,pairKernel_neg,norm_neg] using rightRoot_pair_norm hr hr1 hn
    (y := -y) (v := -v) (by simpa using hy) (by simpa using hv)

theorem leftRoot_pairProduct_norm {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖=r) :
    ‖First.pairProduct (fun i => leftRoot s (y i))‖ ≤ 1 := by
  unfold First.pairProduct
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun j _ => leftRoot_pair_norm hr hr1 hm (hy i) (hy j))

theorem compact_leftRoot_inverse_bound {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : ∀ s ∈ K, s ≠ 0)
    (hm : ∀ s ∈ K, 1+r⁻¹ < -(sourceS s).re) :
    ∃ A, 0 < A ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖=r → ‖(leftRoot s y)⁻¹‖ ≤ A := by
  have hsn : ∀ s ∈ (fun s : ℂ => -s) '' K, s ≠ 0 := by
    rintro s ⟨t,ht,rfl⟩
    exact neg_ne_zero.mpr (hs t ht)
  have hmn : ∀ s ∈ (fun s : ℂ => -s) '' K, 1+r⁻¹ < (sourceS s).re := by
    rintro s ⟨t,ht,rfl⟩
    simpa only [sourceS_neg,Complex.neg_re] using hm t ht
  obtain ⟨A,hA,hb⟩ := compact_rightRoot_inverse_bound (hK.image continuous_neg) hr hr1 hsn hmn
  refine ⟨A,hA,?_⟩
  intro s hsk y hy
  simpa only [leftRoot,inv_neg,norm_neg] using hb (-s) ⟨s,hsk,rfl⟩ (-y) (by simpa using hy)

end
end IsingBulk.HT.Final
