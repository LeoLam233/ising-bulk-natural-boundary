import IsingBulk.HT22.Physical.RealIdentification
import IsingBulk.Anisotropic.FormFactors.ParticleLatticeExchange
import IsingBulk.Anisotropic.Final.IsotropicCoefficients
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Reuse of the genuinely identical all-site/all-particle absolute contour
estimate. The ANISO source uses the same isotropic angular site coefficient;
its Schur-Hadamard envelope is compact-real physics, not a boundary tail. -/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.HT.Contour IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open scoped BigOperators

theorem full_odd_lattice_norm_summable {t : ℝ} (ht : 1<t) :
    Summable (fun p : ℕ × (ℤ × ℤ) =>
      ‖physicalFullLatticeCoefficient (2*p.1+1) t p.2‖) := by
  have hx : 0<Real.arsinh t := Real.arsinh_pos_iff.mpr (by linarith)
  have hp : realProduct 1 (Real.arsinh t)≠1 := by
    rw [realProduct_one,Real.sinh_arsinh]
    nlinarith
  have hs := selected_particle_lattice_norm_summable (by norm_num : (0:ℝ)<1) hx hp
    (fun n => 2*n+1) (fun _ => by omega) (fun _ hC => hadamardEnvelope_odd_summable hC)
  simpa only [realB_one hx,realC_one hx,Real.sinh_arsinh,latticeCoefficient_isotropic] using hs

/-- The exchange is an actual absolutely convergent interchange over every
positive odd particle and every square-lattice site, including the origin. -/
theorem oddSeries_real_eq_siteFirst {t : ℝ} (ht : 1<t) :
    oddSeries (t:ℂ) =
      ∑' v : ℤ × ℤ, ∑' n : ℕ, physicalFullLatticeCoefficient (2*n+1) t v := by
  rw [oddSeries_real_eq_fullLattice ht]
  exact (Summable.tsum_comm (f := fun n v => physicalFullLatticeCoefficient (2*n+1) t v)
    (full_odd_lattice_norm_summable ht).of_norm).symm

theorem odd_site_norm_summable {t : ℝ} (ht : 1<t) (v : ℤ × ℤ) :
    Summable (fun n : ℕ => ‖physicalFullLatticeCoefficient (2*n+1) t v‖) := by
  have hi : Function.Injective (fun n : ℕ => (n,v)) := by
    intro i j h
    exact congrArg Prod.fst h
  simpa only [Function.comp_def] using (full_odd_lattice_norm_summable ht).comp_injective hi

end
end IsingBulk.HT22.Physical
