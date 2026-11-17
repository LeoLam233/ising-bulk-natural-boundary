import IsingBulk.AnisoF002.C03.IsotropicPhysicalDomains

/-!
# Noncritical isotropic points are dense on both complete frontiers

Only the real and imaginary axes of the physical sinh coordinate are
excluded temporarily. Their missing HT tips and every LT contact are
recovered by closure of the actual original frontier graphs.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open Set Filter

def isotropicNoncriticalBoundary (D : Set ℂ) : Set ℂ :=
  {z | z ∈ frontier D ∧ (Complex.sinh z).re ≠ 0 ∧ (Complex.sinh z).im ≠ 0}

theorem isotropic_trig_product_locally_nonzero (y : ℝ) :
    ∀ᶠ t in 𝓝[≠] y, Real.sin t * Real.cos t ≠ 0 := by
  have ha (t : ℝ) : AnalyticAt ℝ (fun u => Real.sin u * Real.cos u) t :=
    Real.analyticAt_sin.mul Real.analyticAt_cos
  rcases (ha y).eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · have hglobal : AnalyticOnNhd ℝ (fun t => Real.sin t * Real.cos t) univ := fun t _ => ha t
    have hall := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ y) hz
    have hh := hall (mem_univ (Real.pi / 4))
    have hs : 0 < Real.sin (Real.pi / 4) := Real.sin_pos_of_pos_of_lt_pi
      (by positivity) (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos (Real.pi / 4) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact False.elim ((ne_of_gt (mul_pos hs hc)) hh)
  · exact hn

theorem isotropic_trig_product_nonzero_dense : Dense {y : ℝ | Real.sin y * Real.cos y ≠ 0} := by
  intro y
  exact ((isotropic_trig_product_locally_nonzero y).frequently.filter_mono nhdsWithin_le_nhds).mem_closure

theorem isotropic_low_noncritical_dense :
    closure (isotropicNoncriticalBoundary (omegaL 1)) = frontier (omegaL 1) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) isClosed_frontier
  · intro z hz
    have hz' : lowProfileF002 1 z.im = z.re := by
      change z ∈ frontier (omegaLF002 1) at hz
      simpa only [frontier_omegaLF002 (by norm_num : (0 : ℝ) < 1), mem_ofPred_eq] using hz
    let g : ℝ → ℂ := fun y => (lowProfileF002 1 y : ℂ) + (y : ℂ) * Complex.I
    have hg : Continuous g :=
      (Complex.continuous_ofReal.comp (lowProfile_continuous (by norm_num : (0 : ℝ) < 1))).add
        (Complex.continuous_ofReal.mul continuous_const)
    have himage := mem_closure_image hg.continuousAt (isotropic_trig_product_nonzero_dense z.im)
    have hsub : g '' {y : ℝ | Real.sin y * Real.cos y ≠ 0} ⊆ isotropicNoncriticalBoundary (omegaL 1) := by
      rintro w ⟨y, hy, rfl⟩
      have hs := (mul_ne_zero_iff.mp hy).1
      have hc := (mul_ne_zero_iff.mp hy).2
      refine ⟨?_, ?_, ?_⟩
      · change g y ∈ frontier (omegaLF002 1)
        rw [frontier_omegaLF002 (by norm_num : (0 : ℝ) < 1)]
        simp [g]
      · rw [complex_sinh_re]
        simp only [g, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add, isotropic_lowProfile_sinh]
        exact mul_ne_zero (abs_ne_zero.mpr hc) hc
      · rw [complex_sinh_im]
        apply mul_ne_zero (ne_of_gt (Real.cosh_pos _))
        simpa only [g, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] using hs
    have hh := closure_mono hsub himage
    have he : g z.im = z := by apply Complex.ext <;> simp [g, hz']
    rwa [he] at hh

theorem isotropic_safe_heights_closure :
    Icc (-Real.pi / 2) (Real.pi / 2) ⊆
      closure (Ioo (-Real.pi / 2) (Real.pi / 2) ∩
        {y : ℝ | Real.sin y * Real.cos y ≠ 0}) := by
  have hs := isotropic_trig_product_nonzero_dense.open_subset_closure_inter
    (isOpen_Ioo : IsOpen (Ioo (-Real.pi / 2) (Real.pi / 2)))
  have hh := closure_mono hs
  rw [closure_closure, closure_Ioo (by linarith [Real.pi_pos] : -Real.pi / 2 ≠ Real.pi / 2)] at hh
  exact hh

theorem isotropic_high_graph_noncritical_closure {e y : ℝ} (he : e = 1 ∨ e = -1)
    (hy : |y| ≤ Real.pi / 2) :
    (((e * highProfileF002 1 y : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈
      closure (isotropicNoncriticalBoundary (omegaH 1)) := by
  let g : ℝ → ℂ := fun t => ((e * highProfileF002 1 t : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hg : Continuous g := (Complex.continuous_ofReal.comp
    (continuous_const.mul (highProfile_continuous (by norm_num : (0 : ℝ) < 1)))).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hh := mem_closure_image hg.continuousAt
    (isotropic_safe_heights_closure (by simpa only [neg_div, mem_Icc] using abs_le.mp hy))
  apply closure_mono ?_ hh
  rintro w ⟨t, ⟨ht, hprod⟩, rfl⟩
  have ht' : |t| < highStripWidthF002 1 := by
    rw [isotropic_strip_width]
    apply abs_lt.mpr
    simpa only [neg_div, mem_Ioo] using ht
  have hp := highProfile_pos (by norm_num : (0 : ℝ) < 1) ht'
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hx : (g t).re ≠ 0 := by simpa only [g, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_self, add_zero] using mul_ne_zero he0 hp.ne'
  refine ⟨?_, ?_, ?_⟩
  · change g t ∈ frontier (omegaHF002 1)
    rw [frontier_omegaHF002 (by norm_num : (0 : ℝ) < 1)]
    change |(g t).im| ≤ highStripWidthF002 1 ∧ |(g t).re| = highProfileF002 1 (g t).im
    simpa [g, abs_mul, heabs, abs_of_pos hp] using ht'.le
  · rw [complex_sinh_re]
    apply mul_ne_zero (Real.sinh_ne_zero.mpr hx)
    simpa [g] using (mul_ne_zero_iff.mp hprod).2
  · rw [complex_sinh_im]
    apply mul_ne_zero (ne_of_gt (Real.cosh_pos _))
    simpa [g] using (mul_ne_zero_iff.mp hprod).1

theorem isotropic_high_noncritical_dense :
    closure (isotropicNoncriticalBoundary (omegaH 1)) = frontier (omegaH 1) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) isClosed_frontier
  · intro z hz
    have hz' : |z.im| ≤ highStripWidthF002 1 ∧ |z.re| = highProfileF002 1 z.im := by
      change z ∈ frontier (omegaHF002 1) at hz
      simpa only [frontier_omegaHF002 (by norm_num : (0 : ℝ) < 1), mem_ofPred_eq] using hz
    have hy : |z.im| ≤ Real.pi / 2 := by simpa only [isotropic_strip_width] using hz'.1
    by_cases hx : 0 ≤ z.re
    · have hh := isotropic_high_graph_noncritical_closure (Or.inl rfl) hy
      have he : (((1 : ℝ) * highProfileF002 1 z.im : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [← hz'.2, abs_of_nonneg hx]
      rwa [he] at hh
    · have hh := isotropic_high_graph_noncritical_closure (Or.inr rfl) hy
      have he : (((-1 : ℝ) * highProfileF002 1 z.im : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [← hz'.2, abs_of_neg (lt_of_not_ge hx)]
      rwa [he] at hh

end IsingBulk.AnisoF002.Isotropic
