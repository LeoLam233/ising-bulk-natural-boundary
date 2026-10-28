import IsingBulk.HT22.Final.FullSeriesAssembly
import IsingBulk.HT22.Final.BoundaryTransfer
import IsingBulk.HT22.Finite.FirstTheorem
import IsingBulk.HT22.Finite.LowerTheorem
import IsingBulk.HT22.PhysicalScope.RealSpin

/-!
# The independent F001 full high-temperature natural boundary

The actual first coefficient, every finite lower odd coefficient and the
complete infinite upper odd tail are proved by the new constrained-coordinate
route. The old HT natural-boundary/noncancellation endpoints are not used.
The physical application exposes only the real-temperature sitewise input.
-/
namespace IsingBulk.HT22.Final
noncomputable section
open IsingBulk.HT22.Physical IsingBulk.HT22.Arithmetic IsingBulk.PrimeFamily
open IsingBulk.Preferred22 IsingBulk.Branch Filter Set
open scoped Topology BigOperators

theorem actual_prime_full_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    LocalLimit.physicalCriticalLeadingCoefficient p (angle p a)≠0 ∧
    Tendsto (fun ε : ℝ => ε • iteratedDeriv (IsingBulk.HT.First.derivativeOrder p)
      (signedOddSeries (negativeSide (angle p a)))
      (radialParameter (primeBranchData hp hp5 ha).alpha ε)) (𝓝[>] 0)
      (𝓝 (LocalLimit.physicalCriticalLeadingCoefficient p (angle p a))) := by
  refine ⟨LocalLimit.prime_physicalCriticalLeadingCoefficient_ne_zero hp hp5 ha,?_⟩
  apply full_signed_series_limit (primeBranchData hp hp5 ha) hp5
    (hp.odd_of_ne_two (by omega)) (negativeSide (angle p a)) le_rfl
  · intro n hn
    exact Finite.prime_lower_coefficient_limit hp hp5 ha ⟨n,rfl⟩ hn _
  · exact Finite.actual_prime_first_limit hp hp5 ha

theorem actual_prime_no_exterior_extension {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    ¬IsingBulk.Final.HasExteriorExtension oddSeries (angleRoot p a) := by
  apply prime_obstruction_of_finite_limits hp hp5 ha
    (LocalLimit.prime_physicalCriticalLeadingCoefficient_ne_zero hp hp5 ha)
  · intro n hn
    exact Finite.prime_lower_coefficient_limit hp hp5 ha ⟨n,rfl⟩ hn _
  · exact Finite.actual_prime_first_limit hp hp5 ha

theorem actual_prime_family_no_exterior_extension :
    ∀ z∈Arithmetic.primeRootFamily,¬IsingBulk.Final.HasExteriorExtension oddSeries z := by
  rintro z ⟨p,a,hp,hp5,ha,rfl⟩
  exact actual_prime_no_exterior_extension hp hp5 ha

/-- Both exact analytic physical germs have the whole unit circle as a
natural boundary, including all four axes. The physical coupling is every J>0. -/
theorem f001_natural_boundary :
    AnalyticOnNhd ℂ interiorBulk {s : ℂ | ‖s‖<1} ∧
    (∀ z : ℂ,‖z‖=1 → ¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z) ∧
    (∀ J : ℝ,0<J → AnalyticOnNhd ℂ (physicalSusceptibility J) {s : ℂ | ‖s‖<1} ∧
      ∀ z : ℂ,‖z‖=1 → ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) z) := by
  obtain ⟨hbulk,hphys⟩ := boundary_transfer_of_prime_obstructions actual_prime_family_no_exterior_extension
  exact ⟨interiorBulk_analyticOn,hbulk,fun J hJ => ⟨physicalSusceptibility_analyticOn hJ,hphys J hJ⟩⟩

/-- Full-lattice real physical application. Its sole external fields are
real-temperature spin-square and sitewise form-factor identities. -/
theorem f001_full_lattice_physical {corr : ℝ → PhysicalScope.LatticeSite → ℝ}
    (hphys : PhysicalScope.PublishedRealHTSpinFormFactors corr) {J : ℝ} (hJ : 0<J) :
    (∀ s : ℝ,0<s → s<1 →
      Summable (fun v => |corr s v|) ∧
      (PhysicalScope.realBulk corr s:ℂ)=interiorBulk (s:ℂ) ∧
      (PhysicalScope.realSusceptibility J corr s:ℂ)=physicalSusceptibility J (s:ℂ) ∧
      PhysicalScope.realBulk corr s=1+∑' v : PhysicalScope.LatticeSite,
        if v=(0,0) then 0 else corr s v) ∧
    AnalyticOnNhd ℂ interiorBulk {s : ℂ | ‖s‖<1} ∧
    AnalyticOnNhd ℂ (physicalSusceptibility J) {s : ℂ | ‖s‖<1} ∧
    (∀ z : ℂ,‖z‖=1 → ¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z) ∧
    (∀ z : ℂ,‖z‖=1 → ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) z) := by
  refine ⟨?_,f001_natural_boundary.1,(f001_natural_boundary.2.2 J hJ).1,
    f001_natural_boundary.2.1,(f001_natural_boundary.2.2 J hJ).2⟩
  intro s hs hs1
  exact ⟨PhysicalScope.realSpin_absolute_summability hphys hs hs1,
    (PhysicalScope.realBulk_summable_and_eq hphys hs hs1).2,
    PhysicalScope.realSusceptibility_eq_physicalGerm J hphys hs hs1,
    PhysicalScope.realBulk_origin_add_offOrigin hphys hs hs1⟩

end
end IsingBulk.HT22.Final
