import IsingBulk.HT22.Controls.Basic
import IsingBulk.HT22.Final.NaturalBoundary

/-! Literal scope specializations of the new endpoint; no old HT endpoint is
invoked. These are implementation controls, not independent audit results. -/
namespace IsingBulk.HT22.Controls
noncomputable section
open PhysicalScope Physical Arithmetic IsingBulk.PrimeFamily IsingBulk.Branch Filter
open scoped Topology

/-- Both physical observables are tested at every boundary point and every
positive coupling, not just one selected prime or one coupling. -/
theorem every_positive_coupling_both_functions (J : ℝ) (hJ : 0<J)
    (z : ℂ) (hz : ‖z‖=1) :
    ¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z ∧
    ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) z :=
  ⟨Final.f001_natural_boundary.2.1 z hz,
    (Final.f001_natural_boundary.2.2 J hJ).2 z hz⟩

/-- All four axes, where the selected-prime formula itself is not applied. -/
theorem all_four_axes (J : ℝ) (hJ : 0<J) :
    ∀ z : ℂ, z∈({1,-1,Complex.I,-Complex.I} : Set ℂ) →
      ¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z ∧
      ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) z := by
  intro z hz
  apply every_positive_coupling_both_functions J hJ z
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

/-- Positive and negative boundary halves are both explicit instantiations. -/
theorem both_boundary_signs (J : ℝ) (hJ : 0<J) (z : ℂ) (hz : ‖z‖=1) :
    (¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z ∧
     ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) z) ∧
    (¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk (-z) ∧
     ¬IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility J) (-z)) :=
  ⟨every_positive_coupling_both_functions J hJ z hz,
    every_positive_coupling_both_functions J hJ (-z) (by simpa using hz)⟩

/-- The two selected p=5 points genuinely exercise different effective signed
charts; the negative branch is not an unused Bool parameter. -/
theorem selected_both_effective_signs :
    negativeSide (angle 5 1)=false ∧ negativeSide (angle 5 2)=true := by
  have hpi := Real.pi_pos
  constructor
  · have hh : ¬Real.pi/2<angle 5 1 := by
      unfold angle
      norm_num
      linarith
    simp [negativeSide,hh]
  · have hh : Real.pi/2<angle 5 2 := by
      unfold angle
      norm_num
      linarith
    simp [negativeSide,hh]

/-- Each effective sign has an actual, proved nonzero full-series prime limit,
not just an abstract signed-kernel type. -/
theorem both_effective_signs_have_actual_prime_limit (negative : Bool) :
    ∃ a : ℤ, ∃ ha : PrimeIndex 5 a,
      negativeSide (angle 5 a)=negative ∧
      LocalLimit.physicalCriticalLeadingCoefficient 5 (angle 5 a)≠0 ∧
      Tendsto (fun ε : ℝ => ε • iteratedDeriv (IsingBulk.HT.First.derivativeOrder 5)
        (signedOddSeries (negativeSide (angle 5 a)))
        (radialParameter (primeBranchData (by norm_num) (by norm_num) ha).alpha ε))
        (𝓝[>] 0) (𝓝 (LocalLimit.physicalCriticalLeadingCoefficient 5 (angle 5 a))) := by
  cases negative with
  | false =>
    have ha : PrimeIndex 5 1 := ⟨by norm_num,by norm_num⟩
    exact ⟨1,ha,selected_both_effective_signs.1,
      Final.actual_prime_full_limit (by norm_num) (by norm_num) ha⟩
  | true =>
    have ha : PrimeIndex 5 2 := ⟨by norm_num,by norm_num⟩
    exact ⟨2,ha,selected_both_effective_signs.2,
      Final.actual_prime_full_limit (by norm_num) (by norm_num) ha⟩

/-- The physical beta normalization is a genuine nonzero divisor on the
entire published real-temperature domain, for every positive J. -/
theorem beta_normalization (J : ℝ) (hJ : 0<J)
    (corr : ℝ → LatticeSite → ℝ) {s : ℝ} (hs : 0<s) :
    0<Real.arsinh s/(2*J) ∧
    realSusceptibility J corr s/(Real.arsinh s/(2*J))=realBulk corr s := by
  have hbeta := (real_temperature_coordinate hJ hs).1
  refine ⟨hbeta,?_⟩
  unfold realSusceptibility
  exact mul_div_cancel_left₀ _ (ne_of_gt hbeta)

/-- Positivity of J is essential: at J=0 the literal beta-inclusive function
is identically zero and extends everywhere. -/
theorem zero_coupling_extends (z : ℂ) :
    IsingBulk.HT.Final.HasInteriorExtension (physicalSusceptibility 0) z := by
  have hzero : physicalSusceptibility 0=(fun _ : ℂ => 0) := by
    funext s
    simp [physicalSusceptibility,IsingBulk.Final.inverseTemperatureBranch]
  rw [hzero]
  exact constant_has_interior_extension 0 z

/-- The published-real-temperature premise is enough for the exact actual
full-lattice application; no complex physical premise is substituted. -/
theorem real_physical_application {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) (J : ℝ) (hJ : 0<J) :
    ∀ s : ℝ, 0<s → s<1 →
      Summable (fun v => |corr s v|) ∧
      (realBulk corr s:ℂ)=interiorBulk (s:ℂ) ∧
      (realSusceptibility J corr s:ℂ)=physicalSusceptibility J (s:ℂ) ∧
      realBulk corr s=1+∑' v : LatticeSite,if v=(0,0) then 0 else corr s v :=
  (Final.f001_full_lattice_physical hphys hJ).1

end
end IsingBulk.HT22.Controls
