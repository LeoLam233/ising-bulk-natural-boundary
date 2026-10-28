import IsingBulk.HT22.Final.SeriesSplit
import IsingBulk.HT22.Physical.GermBridge
import IsingBulk.HT22.Arithmetic.FullFamily
import IsingBulk.HT.Final.DenseBoundary
import IsingBulk.HT.Final.SelectedPhysicalFactors
import IsingBulk.HT.Final.PhysicalConjugation
import IsingBulk.HT.Final.Inversion

/-! Analytic and topological transfers for the exact new physical germ.
This is explicitly a transfer lemma: the new full-series prime obstruction
must be proved separately and is not hidden in the target definition. -/
namespace IsingBulk.HT22.Final
noncomputable section
open IsingBulk.Final IsingBulk.HT.Final IsingBulk.PrimeFamily
open IsingBulk.HT22.Arithmetic Set

theorem primeRoot_nonaxis {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    (angleRoot p a)^4≠1 ∧ (angleRoot p a).re≠0 := by
  constructor
  · intro h
    have hd := (primeIndex_primitive hp ha).dvd_of_pow_eq_one 4 h
    have hl := Nat.le_of_dvd (by norm_num : 0<4) hd
    omega
  · intro h
    have hc := primeRoot_level_ne_zero hp hp5 ha
    apply hc
    have he : Real.cos (angle p a)=0 := by
      simpa only [angleRoot,Complex.exp_ofReal_mul_I_re] using h
    rw [he,mul_zero]

def exteriorPhysical (J : ℝ) (t : ℂ) : ℂ :=
  inverseTemperatureBranch J t⁻¹*Physical.exteriorBulk t

theorem exteriorBulk_conjugate {t : ℂ} (ht : 1<‖t‖) :
    Physical.exteriorBulk (star t)=star (Physical.exteriorBulk t) := by
  have hc := signedOddSeries_conjugate false ht
  change Physical.oddSeries (star t)=star (Physical.oddSeries t) at hc
  simp only [Physical.exteriorBulk,exteriorPrefactor_conjugate ht,hc,star_mul,mul_comm]

theorem exteriorPhysical_conjugate (J : ℝ) {t : ℂ} (ht : 1<‖t‖) :
    exteriorPhysical J (star t)=star (exteriorPhysical J t) := by
  have hi : ‖t⁻¹‖<1 := by rw [norm_inv];exact inv_lt_one_of_one_lt₀ ht
  have hs : |(t⁻¹).im|<1 := (Complex.abs_im_le_norm _).trans_lt hi
  simp only [exteriorPhysical,←star_inv₀,inverseTemperatureBranch_conjugate_strip J hs,
    exteriorBulk_conjugate ht,star_mul,mul_comm]

theorem interiorBulk_eq_exterior_new {s : ℂ} (hs : s≠0) :
    Physical.interiorBulk s=Physical.exteriorBulk s⁻¹ := by
  rw [Physical.interiorBulk_eq_punctured hs]
  unfold Physical.puncturedInteriorBulk Physical.exteriorBulk
  have he := interiorPrefactor_inv s⁻¹
  simpa only [inv_inv] using congrArg (fun z => z*Physical.oddSeries s⁻¹) he

theorem physicalSusceptibility_eq_exterior_new (J : ℝ) {s : ℂ} (hs : s≠0) :
    Physical.physicalSusceptibility J s=exteriorPhysical J s⁻¹ := by
  simp only [Physical.physicalSusceptibility,exteriorPhysical,inv_inv,
    interiorBulk_eq_exterior_new hs]

/-- All axis points are included by closure of the complete upper prime arc.
Only the F001 prime-family obstruction remains a hypothesis here. -/
theorem boundary_transfer_of_prime_obstructions
    (hprime : ∀ z∈primeRootFamily, ¬HasExteriorExtension Physical.oddSeries z) :
    (∀ z : ℂ, ‖z‖=1 → ¬HasInteriorExtension Physical.interiorBulk z) ∧
    (∀ J : ℝ, 0<J → ∀ z : ℂ, ‖z‖=1 →
      ¬HasInteriorExtension (Physical.physicalSusceptibility J) z) := by
  have hdense (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
      unitAngle θ∈closure primeRootFamily := primeRoot_family_dense_upper_arc hθ hθπ
  have hbulk : ∀ z : ℂ, ‖z‖=1 → ¬HasExteriorExtension Physical.exteriorBulk z := by
    apply unit_circle_no_extension_of_upper_dense (fun _ ht => exteriorBulk_conjugate ht) _ hdense
    intro z hz
    have hsource := hprime z hz
    rcases hz with ⟨p,a,hp,hp5,ha,rfl⟩
    have hreg := exteriorPrefactor_regular_at_unit_nonaxis (Complex.norm_exp_ofReal_mul_I _)
      (primeRoot_nonaxis hp hp5 ha).1
    exact no_extension_mul_analytic_factor hreg.1 hreg.2 hsource
  constructor
  · intro z hz he
    apply inversion_transfers_natural_boundary hbulk z hz
    rcases he with ⟨U,hU,hzU,g,hg,hEq⟩
    refine ⟨U,hU,hzU,g,hg,?_⟩
    intro s hs
    exact (hEq hs).trans (interiorBulk_eq_exterior_new (norm_pos_iff.mp hs.2.1))
  · intro J hJ
    have hphys : ∀ z : ℂ, ‖z‖=1 → ¬HasExteriorExtension (exteriorPhysical J) z := by
      apply unit_circle_no_extension_of_upper_dense (fun _ ht => exteriorPhysical_conjugate J ht) _ hdense
      intro z hz
      have hsource := hprime z hz
      rcases hz with ⟨p,a,hp,hp5,ha,rfl⟩
      have hreg := full_physical_factor_regular_unit hJ (Complex.norm_exp_ofReal_mul_I _)
        (primeRoot_nonaxis hp hp5 ha).1 (primeRoot_nonaxis hp hp5 ha).2
      have h := no_extension_mul_analytic_factor hreg.1 hreg.2 hsource
      have heq : (fun t => inverseTemperatureBranch J t⁻¹*exteriorPrefactor t) * Physical.oddSeries =
          exteriorPhysical J := by
        funext t
        simp only [Pi.mul_apply,exteriorPhysical,Physical.exteriorBulk,mul_assoc]
      rwa [heq] at h
    intro z hz he
    apply inversion_transfers_natural_boundary hphys z hz
    rcases he with ⟨U,hU,hzU,g,hg,hEq⟩
    refine ⟨U,hU,hzU,g,hg,?_⟩
    intro s hs
    exact (hEq hs).trans (physicalSusceptibility_eq_exterior_new J (norm_pos_iff.mp hs.2.1))

end
end IsingBulk.HT22.Final
