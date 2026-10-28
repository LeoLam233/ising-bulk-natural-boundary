import IsingBulk.HT22.Physical.JointLatticeSummability
import IsingBulk.HT22.Physical.GermBridge

/-! Precisely real-temperature sitewise physical input, with no complex or
boundary premise. ONGP (2001), equations (1.9), (1.11), (3.13), (3.17)-(3.20)
identify these coefficients with the zero-field HT two-spin function.
The spin-square normalization is explicit. All particle/site exchanges and
the subsequent angular/germ identity are proved, not added as input fields. -/
namespace IsingBulk.HT22.PhysicalScope
noncomputable section
open IsingBulk.HT.Contour IsingBulk.HT.Final IsingBulk.Final
open scoped BigOperators

abbrev LatticeSite := ℤ × ℤ

/-- Correlation is indexed by real s=sinh(2 beta J). No magnetization
subtraction occurs in the zero-field high-temperature state. -/
structure PublishedRealHTSpinFormFactors (corr : ℝ → LatticeSite → ℝ) : Prop where
  spin_square : ∀ s : ℝ, 0<s → s<1 → corr s (0,0)=1
  sitewise : ∀ s : ℝ, 0<s → s<1 → ∀ v : LatticeSite,
    (corr s v:ℂ)=interiorPrefactor (s:ℂ)*
      ∑' n : ℕ, physicalFullLatticeCoefficient (2*n+1) s⁻¹ v

/-- Literal full-lattice susceptibility divided by physical beta. -/
def realBulk (corr : ℝ → LatticeSite → ℝ) (s : ℝ) : ℝ := ∑' v,corr s v

def realSusceptibility (J : ℝ) (corr : ℝ → LatticeSite → ℝ) (s : ℝ) : ℝ :=
  (Real.arsinh s/(2*J))*realBulk corr s

theorem realBulk_summable_and_eq {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    Summable (corr s) ∧ (realBulk corr s:ℂ)=Physical.interiorBulk (s:ℂ) := by
  have ht : 1<s⁻¹ := (one_lt_inv₀ hs).mpr hs1
  have habs := Physical.full_odd_lattice_norm_summable ht
  have hsite := habs.of_norm.prod_symm.prod
  have hc : Summable (fun v => (corr s v:ℂ)) := by
    simpa only [hphys.sitewise s hs hs1,Prod.swap] using hsite.mul_left (interiorPrefactor (s:ℂ))
  refine ⟨Complex.summable_ofReal.mp hc,?_⟩
  rw [Physical.interiorBulk_eq_punctured (Complex.ofReal_ne_zero.mpr hs.ne')]
  unfold realBulk Physical.puncturedInteriorBulk
  rw [Complex.ofReal_tsum]
  simp_rw [hphys.sitewise s hs hs1]
  rw [tsum_mul_left,←Physical.oddSeries_real_eq_siteFirst ht]
  simp only [Complex.ofReal_inv]

/-- Absolute full-site convergence follows from the proved joint particle /
lattice estimate and the real sitewise identity, not from conditional exchange. -/
theorem realSpin_absolute_summability {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    Summable (fun v : LatticeSite => |corr s v|) := by
  have ht : 1<s⁻¹ := (one_lt_inv₀ hs).mpr hs1
  have habs := Physical.full_odd_lattice_norm_summable ht
  have hmajor : Summable (fun v : LatticeSite =>
      ‖interiorPrefactor (s:ℂ)‖ *
        ∑' n : ℕ, ‖physicalFullLatticeCoefficient (2*n+1) s⁻¹ v‖) := by
    simpa only [Prod.swap] using habs.prod_symm.prod.mul_left ‖interiorPrefactor (s:ℂ)‖
  apply hmajor.of_nonneg_of_le (fun v => abs_nonneg _) 
  intro v
  have h := congrArg norm (hphys.sitewise s hs hs1 v)
  rw [Complex.norm_real,Real.norm_eq_abs,norm_mul] at h
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (norm_tsum_le_tsum_norm (Physical.odd_site_norm_summable ht v)) (norm_nonneg _)

theorem realBulk_origin_add_offOrigin {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    realBulk corr s=1+∑' v : LatticeSite,if v=(0,0) then 0 else corr s v := by
  have h := (realBulk_summable_and_eq hphys hs hs1).1.tsum_eq_add_tsum_ite (0,0)
  simpa only [realBulk,hphys.spin_square s hs hs1] using h

/-- The origin is precisely one after the complete odd sum and physical
prefactor, never one per particle and never omitted from the susceptibility. -/
theorem full_odd_origin_normalization {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    interiorPrefactor (s:ℂ)*
      (∑' n : ℕ,physicalFullLatticeCoefficient (2*n+1) s⁻¹ (0,0))=1 := by
  rw [←hphys.sitewise s hs hs1 (0,0),hphys.spin_square s hs hs1,Complex.ofReal_one]

/-- The physical beta factor is exactly arsinh(s)/(2J), not omitted or
absorbed into the formal-series variable. -/
theorem realSusceptibility_eq_physicalGerm (J : ℝ) {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    (realSusceptibility J corr s:ℂ)=Physical.physicalSusceptibility J (s:ℂ) := by
  unfold realSusceptibility Physical.physicalSusceptibility
  rw [Complex.ofReal_mul,(realBulk_summable_and_eq hphys hs hs1).2,
    inverseTemperatureBranch_real hs.le]
  push_cast
  rfl

theorem real_temperature_coordinate {J s : ℝ} (hJ : 0<J) (hs : 0<s) :
    0<Real.arsinh s/(2*J) ∧ Real.sinh (2*(Real.arsinh s/(2*J))*J)=s := by
  constructor
  · exact div_pos (Real.arsinh_pos_iff.mpr hs) (by positivity)
  · have he : 2*(Real.arsinh s/(2*J))*J=Real.arsinh s := by field_simp
    rw [he,Real.sinh_arsinh]

end
end IsingBulk.HT22.PhysicalScope
