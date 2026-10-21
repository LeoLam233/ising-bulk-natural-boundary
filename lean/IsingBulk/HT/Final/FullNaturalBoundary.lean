import IsingBulk.HT.Final.PositiveFullNoncancellation
import IsingBulk.HT.Final.NegativeFullNoncancellation
import IsingBulk.HT.Final.SelectedFamilyDensity
import IsingBulk.HT.Final.SelectedPhysicalFactors
import IsingBulk.HT.Final.PhysicalConjugation
import IsingBulk.HT.Final.PhysicalIdentification
import IsingBulk.HT.Final.Inversion

/-! Source-level endpoint assembly for the actual complete odd full-site germ.
All selected obstructions and density inputs are proved imported declarations.
The real physical angular representation is a separate identification task;
this file does not assume it or use it as a substitute for an analytic proof. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.Final IsingBulk.HT.First Set

/-- The two original arithmetic families are both obstructed. -/
theorem originalSelectedFamily_no_exterior_extension :
    ∀ z ∈ originalSelectedFamily, ¬ HasExteriorExtension exteriorOddSeries z := by
  intro z hz
  rcases hz with hp | hn
  · rcases hp with ⟨p,a,b,hp,hp11,hab,ha,hb,rfl⟩
    exact selected_positive_exterior_no_extension hp hp11 ha hb hab
  · rcases hn with ⟨p,a,b,hp,hp11,hab,ha,hb,rfl⟩
    exact selected_negative_exterior_no_extension hp hp11 ha hb hab

/-- Every point of the unit circle obstructs continuation of the literal
infinite odd coefficient sum. Endpoint density includes ±1 and ±i. -/
theorem exteriorOddSeries_unit_circle_no_extension :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension exteriorOddSeries z :=
  unit_circle_no_extension_of_upper_dense
    (fun _ ht => exteriorOddSeries_conjugate ht)
    originalSelectedFamily_no_exterior_extension
    (fun _ ht htpi => originalSelectedFamily_dense_closed_upper_arc ht.le htpi.le)

theorem originalSelectedFamily_no_bulk_extension :
    ∀ z ∈ originalSelectedFamily, ¬ HasExteriorExtension exteriorFullBulk z := by
  intro z hz
  have hsource := originalSelectedFamily_no_exterior_extension z hz
  have hreg : AnalyticAt ℂ exteriorPrefactor z ∧ exteriorPrefactor z ≠ 0 := by
    rcases hz with hp | hn
    · rcases hp with ⟨p,a,b,_hp,_hp11,_hab,ha,hb,rfl⟩
      exact exteriorPrefactor_regular_at_unit_nonaxis
        (Complex.norm_exp_ofReal_mul_I _) (selected_positive_nonaxis ha hb).1
    · rcases hn with ⟨p,a,b,_hp,_hp11,_hab,ha,hb,rfl⟩
      exact exteriorPrefactor_regular_at_unit_nonaxis
        (Complex.norm_exp_ofReal_mul_I _) (selected_negative_nonaxis ha hb).1
  exact no_extension_mul_analytic_factor hreg.1 hreg.2 hsource

/-- The actual HT prefactor is retained before dense-boundary propagation. -/
theorem exteriorFullBulk_unit_circle_no_extension :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension exteriorFullBulk z :=
  unit_circle_no_extension_of_upper_dense
    (fun _ ht => exteriorFullBulk_conjugate ht)
    originalSelectedFamily_no_bulk_extension
    (fun _ ht htpi => originalSelectedFamily_dense_closed_upper_arc ht.le htpi.le)

theorem originalSelectedFamily_no_physical_extension {J : ℝ} (hJ : 0 < J) :
    ∀ z ∈ originalSelectedFamily, ¬ HasExteriorExtension (exteriorPhysicalSusceptibility J) z := by
  intro z hz
  have hsource := originalSelectedFamily_no_exterior_extension z hz
  have hreg : AnalyticAt ℂ (fun t => inverseTemperatureBranch J (t⁻¹)*exteriorPrefactor t) z ∧
      inverseTemperatureBranch J (z⁻¹)*exteriorPrefactor z ≠ 0 := by
    rcases hz with hp | hn
    · rcases hp with ⟨p,a,b,_hp,_hp11,_hab,ha,hb,rfl⟩
      exact selected_positive_physical_factor_regular hJ ha hb
    · rcases hn with ⟨p,a,b,_hp,_hp11,_hab,ha,hb,rfl⟩
      exact selected_negative_physical_factor_regular hJ ha hb
  have h := no_extension_mul_analytic_factor hreg.1 hreg.2 hsource
  have heq : (fun t => inverseTemperatureBranch J (t⁻¹)*exteriorPrefactor t) * exteriorOddSeries =
      exteriorPhysicalSusceptibility J := by
    funext t
    simp only [Pi.mul_apply,exteriorPhysicalSusceptibility,exteriorFullBulk,mul_assoc]
  rwa [heq] at h

theorem exteriorPhysicalSusceptibility_unit_circle_no_extension {J : ℝ} (hJ : 0 < J) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension (exteriorPhysicalSusceptibility J) z :=
  unit_circle_no_extension_of_upper_dense
    (fun _ ht => exteriorPhysicalSusceptibility_conjugate J ht)
    (originalSelectedFamily_no_physical_extension hJ)
    (fun _ ht htpi => originalSelectedFamily_dense_closed_upper_arc ht.le htpi.le)

/-- Transfer to the actual disk germ, including its separately constructed
removable value at zero. Local overlap is genuinely open and punctured. -/
theorem interiorFullBulk_unit_circle_no_extension :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasInteriorExtension interiorFullBulk z := by
  intro z hz he
  apply inversion_transfers_natural_boundary exteriorFullBulk_unit_circle_no_extension z hz
  rcases he with ⟨U,hU,hzU,g,hg,hEq⟩
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq hs).trans (interiorFullBulk_eq_exterior (norm_pos_iff.mp hs.2.1))

theorem interiorPhysicalSusceptibility_unit_circle_no_extension {J : ℝ} (hJ : 0 < J) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z := by
  intro z hz he
  apply inversion_transfers_natural_boundary
    (exteriorPhysicalSusceptibility_unit_circle_no_extension hJ) z hz
  rcases he with ⟨U,hU,hzU,g,hg,hEq⟩
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq hs).trans
    (interiorPhysicalSusceptibility_eq_exterior (norm_pos_iff.mp hs.2.1))

/-- The constructed full HT susceptibility is analytic on the open unit disk
and has no continuation through any point of its boundary. -/
theorem interiorPhysicalSusceptibility_natural_boundary {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      ∀ z : ℂ, ‖z‖=1 → ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z :=
  ⟨interiorPhysicalSusceptibility_analyticOn hJ,
    interiorPhysicalSusceptibility_unit_circle_no_extension hJ⟩

/-- Physical-facing germ theorem. The analytic construction and boundary
obstruction are internal; identifying their real germ with the lattice
susceptibility is conditional on the explicit full odd representation.
No premise about the analytic tail or the first singularity is introduced. -/
theorem physicalSusceptibility_germ_natural_boundary {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PhysicalSusceptibilityRepresentation J chi) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      (∀ x : ℝ, 0 < x → x < 1/16 →
        chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ)) ∧
      ∀ z : ℂ, ‖z‖=1 →
        ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z := by
  exact ⟨interiorPhysicalSusceptibility_analyticOn hJ,
    fun _ hx hxsmall => physicalSusceptibility_real_germ hJ hrep hx hxsmall,
    interiorPhysicalSusceptibility_unit_circle_no_extension hJ⟩

/-- If chi already denotes an analytic disk continuation of the physical
real germ, the conclusion applies to that exact function, not only to a
constructed proxy. Both external identification premises are explicit. -/
theorem physicalSusceptibility_unit_circle_no_extension {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi {s : ℂ | ‖s‖ < 1})
    (hrep : PhysicalSusceptibilityRepresentation J chi) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasInteriorExtension chi z := by
  have hsame := physicalSusceptibility_eqOn_unitDisk hJ hchi hrep
  intro z hz he
  apply interiorPhysicalSusceptibility_unit_circle_no_extension hJ z hz
  rcases he with ⟨U,hU,hzU,g,hg,hEq⟩
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq hs).trans (hsame hs.2.2)

end
end IsingBulk.HT.Final
