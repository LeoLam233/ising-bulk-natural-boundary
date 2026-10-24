import IsingBulk.Anisotropic.Geometry.IsotropicBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace IsingBulk.Anisotropic
noncomputable section
open Filter Topology

theorem cosh_re_formula (z : ℂ) : (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.cosh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cosh_im_formula (z : ℂ) : (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cosh_zero_implies_re_zero {z : ℂ} (hz : Complex.cosh z = 0) : z.re = 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  rw [cosh_re_formula, Complex.zero_re] at hr
  rw [cosh_im_formula, Complex.zero_im] at hi
  have hc : Real.cos z.im = 0 := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (Real.cosh_pos _))
  have hs : Real.sin z.im ≠ 0 := by
    intro h
    have := Real.sin_sq_add_cos_sq z.im
    simp [h,hc] at this
  exact Real.sinh_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right hs)

theorem cosh_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.cosh z ≠ 0 := by
  intro h
  have := cosh_zero_implies_re_zero h
  linarith

theorem dense_cos_ne_zero : Dense {y : ℝ | Real.cos y ≠ 0} := by
  intro y
  rw [mem_closure_iff_frequently]
  by_contra h
  have he : Real.cos =ᶠ[𝓝 y] (fun _ => 0) := by
    change ∀ᶠ x in 𝓝 y, Real.cos x = 0
    simpa only [Set.mem_ofPred_eq, not_not] using Filter.not_frequently.mp h
  have hd := he.deriv_eq
  have hv := he.eq_of_nhds
  simp only [Real.deriv_cos, deriv_const] at hd
  have ht := Real.sin_sq_add_cos_sq y
  rw [hv] at ht
  nlinarith

/-- No ramified LT boundary contact is omitted by the local isotropic pullback. -/
theorem frontier_omegaL_one_subset_closure_noncritical :
    frontier (omegaL 1) ⊆ closure {z | z ∈ frontier (omegaL 1) ∧ Complex.cosh z ≠ 0} := by
  intro z hz
  let g : ℝ → ℂ := fun y => (sliceL 1 y : ℂ) + (y : ℂ)*Complex.I
  have hg : Continuous g := by
    exact (Complex.continuous_ofReal.comp (sliceL_continuous (by norm_num))).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hm : Set.MapsTo g {y | Real.cos y ≠ 0}
      {w | w ∈ frontier (omegaL 1) ∧ Complex.cosh w ≠ 0} := by
    intro y hy
    have hre : (g y).re = sliceL 1 y := by simp [g]
    have him : (g y).im = y := by simp [g]
    refine ⟨(mem_frontier_omegaL_iff (by norm_num) (g y)).mpr (by rw [hre,him]), ?_⟩
    apply cosh_ne_zero_of_re_pos
    rw [hre, sliceL_isotropic]
    exact Real.arsinh_pos_iff.mpr (abs_pos.mpr hy)
  have hz' : g z.im = z := by
    apply Complex.ext
    · simpa [g] using ((mem_frontier_omegaL_iff (by norm_num) z).mp hz).symm
    · simp [g]
  rw [← hz']
  exact hm.closure hg (dense_cos_ne_zero z.im)

/-- The right open arc belongs to the actual HT lens boundary. -/
theorem isotropic_right_arc_frontier {y : ℝ} (hy : |y| < Real.pi/2) :
    ((Real.arsinh (Real.cos y) : ℝ) : ℂ) + (y : ℂ)*Complex.I ∈ frontier (omegaH 1) := by
  let x := Real.arsinh (Real.cos y)
  have hx : 0 < x := Real.arsinh_pos_iff.mpr (Real.cos_pos_of_mem_Ioo (abs_lt.mp hy))
  let g : ℝ → ℂ := fun t => ((t*x : ℝ) : ℂ) + (y : ℂ)*Complex.I
  have hg : Continuous g := by fun_prop
  have hm : Set.MapsTo g (Set.Ioo 0 1) (omegaH 1) := by
    intro t ht
    change |(g t).im| < sliceY 1 ∧ |(g t).re| < sliceH 1 (g t).im
    have htx : 0 < t*x := mul_pos ht.1 hx
    simp only [g, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, sub_zero, sliceH_isotropic,
      abs_of_pos htx]
    constructor
    · simpa [sliceY] using hy
    · change t*x < x
      nlinarith [ht.2]
  have hcl : (1:ℝ) ∈ closure (Set.Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  rw [(omegaH_isOpen (by norm_num : (0:ℝ)<1)).frontier_eq]
  refine ⟨?_, ?_⟩
  · simpa only [g, one_mul] using hm.closure hg hcl
  · intro h
    have h' := h.2
    simp [x, sliceH_isotropic, abs_of_pos hx] at h'

/-- The two HT ramification tips are limits of noncritical points of the same boundary. -/
theorem frontier_omegaH_one_subset_closure_noncritical :
    frontier (omegaH 1) ⊆ closure {z | z ∈ frontier (omegaH 1) ∧ Complex.cosh z ≠ 0} := by
  intro z hz
  by_cases hc : Complex.cosh z ≠ 0
  · exact subset_closure ⟨hz,hc⟩
  push Not at hc
  have hre := cosh_zero_implies_re_zero hc
  have hcos : Real.cos z.im = 0 := by
    have h := congrArg Complex.re hc
    rw [cosh_re_formula, Complex.zero_re] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (Real.cosh_pos _))
  let g : ℝ → ℂ := fun y => ((Real.arsinh (Real.cos y) : ℝ) : ℂ) + (y : ℂ)*Complex.I
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp (Real.continuous_arsinh.comp Real.continuous_cos)).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hm : Set.MapsTo g (Set.Ioo (-(Real.pi/2)) (Real.pi/2))
      {w | w ∈ frontier (omegaH 1) ∧ Complex.cosh w ≠ 0} := by
    intro y hy
    refine ⟨isotropic_right_arc_frontier (abs_lt.mpr hy), ?_⟩
    apply cosh_ne_zero_of_re_pos
    simpa [g] using Real.arsinh_pos_iff.mpr (Real.cos_pos_of_mem_Ioo hy)
  have hcl : z.im ∈ closure (Set.Ioo (-(Real.pi/2)) (Real.pi/2)) := by
    rw [closure_Ioo (by linarith [Real.pi_pos] : -(Real.pi/2) ≠ Real.pi/2)]
    exact abs_le.mp (closure_omegaH_one_bounds (frontier_subset_closure hz)).1
  have hgz : g z.im = z := by
    apply Complex.ext
    · simp [g,hcos,hre]
    · simp [g]
  rw [← hgz]
  exact hm.closure hg hcl

end
end IsingBulk.Anisotropic
