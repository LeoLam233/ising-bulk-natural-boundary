import IsingBulk.Anisotropic.NegativeCycles.PhysicalModelTail

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First MeasureTheory

 theorem quadraticModelKernel_integrable {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (h : ℂ) (hh : 0<h.re) :
    Integrable (quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ))) := by
  apply Integrable.of_integral_ne_zero
  rw [quadraticModelKernel_integral]
  simpa only [Nat.add_sub_cancel] using negativeEdge_complex_period_ne_zero ho (by omega) j hj h hh

 theorem quadraticModel_cutoff_integrable {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (h : ℂ) (hh : 0<h.re) (b : ContDiffBump (0:ℝ)) :
    Integrable (fun q : Fin n→ℝ => (shapeSpatialCutoff b q:ℂ)*
      quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ)) q) := by
  have hi := quadraticModelKernel_integrable ho hn j hj h hh
  have hcut : Continuous (fun q : Fin n→ℝ => (shapeSpatialCutoff b q:ℂ)) :=
    Complex.continuous_ofReal.comp (shapeSpatialCutoff_contDiff b 0).continuous
  apply hi.norm.mono' (hcut.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  simp only [Pi.mul_apply]
  rw [norm_mul]
  have hnorm : ‖(shapeSpatialCutoff b q:ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤shapeSpatialCutoff b q from b.nonneg)]
    exact b.le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

 theorem quadraticModel_cutoff_sub_period {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (h : ℂ) (hh : 0<h.re) (b : ContDiffBump (0:ℝ)) :
    (∫q : Fin n→ℝ,(shapeSpatialCutoff b q:ℂ)*
      quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ)) q)-
        shapePeriod n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ))=
      -(∫q : Fin n→ℝ,(1-(shapeSpatialCutoff b q:ℂ))*
        quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ)) q) := by
  have hi := quadraticModelKernel_integrable ho hn j hj h hh
  have hb := quadraticModel_cutoff_integrable ho hn j hj h hh b
  simp_rw [sub_mul,one_mul]
  rw [integral_sub hi hb,quadraticModelKernel_integral]
  ring

 theorem physical_model_cutoff_comparison {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : 2*alpha (n+1)≤j) (h : ℂ) (hh : (1:ℝ)/2≤h.re)
    (b : ContDiffBump (0:ℝ)) (hlarge : 32*Real.pi^2≤(n+1:ℕ)*b.rIn) :
    ‖(∫q : Fin n→ℝ,(shapeSpatialCutoff b q:ℂ)*
      quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ)) q)-
        shapePeriod n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ))‖≤
      ((1/2:ℝ)^j*(‖h‖/h.re)^(alpha (n+1)))*
        ‖shapePeriod n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ))‖ := by
  rw [quadraticModel_cutoff_sub_period ho hn j (by omega) h (by linarith) b,norm_neg]
  exact physical_model_cutoff_tail ho hn j hj h hh b hlarge

end IsingBulk.Anisotropic.NegativeCycles
