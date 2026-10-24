import IsingBulk.Anisotropic.Final.LocalExtension
import IsingBulk.Anisotropic.NegativeDominance.ZeroRadius
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Boundary jets identify the Taylor series of any genuine local extension.
The proof uses agreement on an open overlap, not equality merely on a ray. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter
open scoped Topology

/-- Every normalized inward derivative limit equals the Taylor coefficient
of an extension on its open overlap. The path and its filter are arbitrary. -/
theorem boundary_jet_eq_extension_coefficient
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {D U : Set ℂ} {f g : ℂ → ℂ} {z a : ℂ}
    (hD : IsOpen D) (hU : IsOpen U) (hzU : z ∈ U)
    (hg : AnalyticOnNhd ℂ g U) (heq : EqOn g f (U ∩ D))
    (hpath : Tendsto path l (𝓝 z)) (hinside : ∀ᶠ t in l, path t ∈ D)
    (j : ℕ)
    (hjet : Tendsto (fun t => iteratedDeriv j f (path t) / (j.factorial : ℂ)) l (𝓝 a)) :
    a = iteratedDeriv j g z / (j.factorial : ℂ) := by
  have hUevent := hpath.eventually (hU.mem_nhds hzU)
  have hderiv : ∀ᶠ t in l, iteratedDeriv j f (path t) = iteratedDeriv j g (path t) := by
    filter_upwards [hUevent, hinside] with t htU htD
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [(hU.inter hD).mem_nhds ⟨htU, htD⟩] with w hw
    exact (heq hw).symm
  have hcont : ContinuousAt (iteratedDeriv j g) z := by
    simpa only [iteratedDeriv_eq_iterate] using ((hg z hzU).iterated_deriv j).continuousAt
  have hlim : Tendsto (fun t => iteratedDeriv j g (path t) / (j.factorial : ℂ)) l
      (𝓝 (iteratedDeriv j g z / (j.factorial : ℂ))) :=
    (hcont.tendsto.comp hpath).div_const _
  apply tendsto_nhds_unique hjet
  apply hlim.congr'
  filter_upwards [hderiv] with t ht
  rw [ht]

/-- Zero radius of the actual inward jets rules out a true domain extension.
This directly uses `HasDomainExtension`, the final project's predicate. -/
theorem no_domain_extension_of_boundary_jets_zero_radius
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (a : ℕ → ℂ)
    (hD : IsOpen D) (hpath : Tendsto path l (𝓝 z))
    (hinside : ∀ᶠ t in l, path t ∈ D)
    (hjets : ∀ j, Tendsto (fun t => iteratedDeriv j f (path t) / (j.factorial : ℂ)) l (𝓝 (a j)))
    (hz : (FormalMultilinearSeries.ofScalars ℂ a).radius = 0) :
    ¬ HasDomainExtension D f z := by
  rintro ⟨U, hU, hzU, g, hg, heq⟩
  have ha : a = fun j => iteratedDeriv j g z / (j.factorial : ℂ) := by
    funext j
    exact boundary_jet_eq_extension_coefficient hD hU hzU hg heq hpath hinside j (hjets j)
  apply not_hasFPowerSeriesAt_of_zero_radius a hz g z
  rw [ha]
  exact (hg z hzU).hasFPowerSeriesAt

/-- Selected-order supergeometric growth of the actual boundary jets is
sufficient for the whole-germ obstruction, with no restriction on phases. -/
theorem no_domain_extension_of_boundary_jets_unbounded
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (a : ℕ → ℂ) (orders : ℕ → ℕ)
    (hD : IsOpen D) (hpath : Tendsto path l (𝓝 z))
    (hinside : ∀ᶠ t in l, path t ∈ D)
    (hjets : ∀ j, Tendsto (fun t => iteratedDeriv j f (path t) / (j.factorial : ℂ)) l (𝓝 (a j)))
    (hgrowth : ∀ r : ℝ, 0 < r → ∀ C : ℝ,
      ∃ n, C < ‖a (orders n)‖ * r ^ orders n) :
    ¬ HasDomainExtension D f z :=
  no_domain_extension_of_boundary_jets_zero_radius a hD hpath hinside hjets
    (scalar_radius_eq_zero_of_subsequence a orders hgrowth)

end
end IsingBulk.Anisotropic.NegativeDominance
