import IsingBulk.Anisotropic.Final.IsotropicLowCoefficients
import IsingBulk.Anisotropic.FormFactors.PhysicalCovariance

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors IsingBulk.HT.Contour IsingBulk.First IsingBulk.Tail

theorem isotropic_latticeCoefficient_real (N : ℕ) {x : ℝ} (hx : 0<x) (v : LatticeSite) :
    latticeCoefficient N (realB 1 x) (realC 1 x) v =
      physicalFullLatticeCoefficient N (Real.sinh x) v := by
  rw [realB_one hx,realC_one hx,latticeCoefficient_isotropic]

theorem isotropic_even_onsite_summable {x : ℝ} (hx : criticalPoint 1<x) :
    Summable (fun n : ℕ => physicalFullLatticeCoefficient (2*n+2) (Real.sinh x) (0,0)) := by
  obtain ⟨hx0,_hs,hp⟩ := isotropic_low_real_parameters hx
  have hh := selected_particle_lattice_norm_summable (by norm_num : (0:ℝ)<1) hx0 hp
    (fun n => 2*n+2) (fun _ => by omega) (fun _ hC => even_positive_envelope_summable hC)
  have hi : Function.Injective (fun n : ℕ => ((n,(0,0)):ℕ×LatticeSite)) := by
    intro i j he
    exact congrArg Prod.fst he
  have h := hh.of_norm.comp_injective hi
  simpa only [Function.comp_def,isotropic_latticeCoefficient_real _ hx0] using h

theorem isotropic_realMagnetization_eq {x : ℝ} (hx : criticalPoint 1<x) :
    (realMagnetizationSq 1 x:ℂ)=magnetizationSquared (Real.sinh x:ℂ) := by
  have ht := lowRealRadicand_pos (by norm_num : (0:ℝ)<1) hx
  have ht' : 0≤1-(realProduct 1 x)⁻¹^2 := ht.le
  unfold realMagnetizationSq
  rw [Complex.ofReal_cpow ht']
  simp only [realProduct_one,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,magnetizationSquared]
  congr 1
  ring_nf

theorem isotropic_low_real_eq {x : ℝ} (hx : criticalPoint 1<x)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors 1 corrH corrL) :
    lowNormalizedBulk 1 (x:ℂ)=exteriorNormalizedBulk (Real.sinh x:ℂ) := by
  obtain ⟨hx0,hs,_hp⟩ := isotropic_low_real_parameters hx
  have hp : 1<realProduct 1 x := by rw [realProduct_one]; nlinarith
  have ho := hphys.low_spin x hx0 hp (0,0)
  rw [hphys.low_onsite x hx0 hp] at ho
  simp only [Complex.ofReal_one,evenSiteSeries,isotropic_latticeCoefficient_real _ hx0] at ho
  have hon := isotropic_even_onsite_summable hx
  have hoff : Summable (fun n : ℕ => exteriorEvenTerm n (Real.sinh x:ℂ)) := by
    have hnorm : 1<‖(Real.sinh x:ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hs)]
      exact hs
    simpa only [iteratedDeriv_zero] using (exteriorEven_derivative_summable 0 hnorm).of_norm
  unfold lowNormalizedBulk
  simp_rw [isotropic_low_weighted_term _ hx]
  rw [hon.tsum_add (hoff.mul_left 2),tsum_mul_left,lowPrefactor_real (by norm_num) hx]
  unfold exteriorNormalizedBulk exteriorEvenSeries
  rw [← isotropic_realMagnetization_eq hx]
  linear_combination -ho

end
end IsingBulk.Anisotropic
