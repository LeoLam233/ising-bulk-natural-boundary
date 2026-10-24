import IsingBulk.Anisotropic.NegativeCycles.ConstrainedCylinderCutoff

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter Metric
open scoped Topology BigOperators

theorem constrainedSquaredRadius_fderiv_single {n : ℕ} (q : Fin n→ℝ) (i : Fin n) :
    fderiv ℝ constrainedSquaredRadius q (Pi.single i 1)=2*(q i+∑j,q j) := by
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (ContinuousLinearMap.proj j : (Fin n→ℝ)→L[ℝ]ℝ).hasFDerivAt (x := q))
  have hsq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((ContinuousLinearMap.proj j : (Fin n→ℝ)→L[ℝ]ℝ).hasFDerivAt (x := q)).pow 2)
  have hh := hsq.fun_add (hsum.pow 2)
  simp only [ContinuousLinearMap.proj_apply] at hh
  have he : @constrainedSquaredRadius n=(fun q => (∑j,q j^2)+(∑j,q j)^2) :=
    funext constrainedSquaredRadius_eq
  rw [he,hh.fderiv]
  simp [Finset.mul_sum,Pi.single_apply]
  rw [←Finset.mul_sum]
  ring

theorem constrainedSquaredRadius_coordinates_le {n : ℕ} (q : Fin n→ℝ) {r : ℝ}
    (hr : 0≤r) (hq : constrainedSquaredRadius q≤r^2) :
    (∀i,|q i|≤r) ∧ |∑i,q i|≤r := by
  have hs : 0≤squaredRadius q := squaredRadius_nonneg q
  rw [constrainedSquaredRadius_eq] at hq
  constructor
  · intro i
    have hi : q i^2≤squaredRadius q := Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
    exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by rw [_root_.sq_abs]; nlinarith [sq_nonneg (∑j,q j)])
  · exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by rw [_root_.sq_abs]; linarith)

theorem shapeSpatialCutoff_fderiv_single {n : ℕ} (b : ContDiffBump (0:ℝ))
    (q : Fin n→ℝ) (i : Fin n) :
    fderiv ℝ (shapeSpatialCutoff b) q (Pi.single i 1)=
      deriv b (constrainedSquaredRadius q)*(2*(q i+∑j,q j)) := by
  have hb := (((b.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt (x := constrainedSquaredRadius q)).hasDerivAt
  have hq := (constrainedSquaredRadius_contDiff (n := n) 1).differentiable (by norm_num)
  change fderiv ℝ (b ∘ constrainedSquaredRadius) q _=_
  rw [(hb.comp_hasFDerivAt q hq.differentiableAt.hasFDerivAt).fderiv]
  simp only [smul_apply,smul_eq_mul,constrainedSquaredRadius_fderiv_single]

/-- A dimension-free gradient bound in the full constrained-radius cutoff. -/
theorem shapeSpatialCutoff_gradient_bound {n : ℕ} (b : ContDiffBump (0:ℝ))
    {q : Fin n→ℝ} {r K : ℝ} (hr : 0≤r) (hK : 0≤K)
    (hq : constrainedSquaredRadius q≤r^2) (hb : ‖deriv b (constrainedSquaredRadius q)‖≤K)
    (i : Fin n) : ‖fderiv ℝ (shapeSpatialCutoff b) q (Pi.single i 1)‖≤K*(4*r) := by
  rw [shapeSpatialCutoff_fderiv_single,norm_mul]
  obtain ⟨hi,hs⟩ := constrainedSquaredRadius_coordinates_le q hr hq
  have hinner : ‖2*(q i+∑j,q j)‖≤4*r := by
    rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),Real.norm_eq_abs]
    have ha := abs_add_le (q i) (∑j,q j)
    nlinarith [hi i]
  exact mul_le_mul hb hinner (norm_nonneg _) hK

end IsingBulk.Anisotropic.NegativeCycles
