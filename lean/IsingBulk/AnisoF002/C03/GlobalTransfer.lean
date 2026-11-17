import IsingBulk.AnisoF002.C03.DomainBridge
import IsingBulk.Anisotropic.Final.AnalyticFactor

/-!
# Global domain-side transfer for the exact physical domains

F002 section 6: the extension contradiction passes to the closure of the
actual obstruction set.  The normalization transfer uses the exact
z/(2J), and the proof includes the nonvanishing check at every frontier
point.  The input nonextensions are still to be supplied by the complete
F002 particle mechanisms; these theorems do not assume them physically.

Historical mathematical content below is limited to HasDomainExtension,
NaturalBoundaryOn, inverseTemperature and the literal geometric definitions.
Their transitive closure also contains the generated numeral certificates
inverseTemperature._proof_1 and sliceY._proof_1, both proving
Nat.AtLeastTwo (1 + 1); these are explicitly inspected by the C03 support
audit. No historical analytic-factor or natural-boundary theorem is reused.
-/

namespace IsingBulk.AnisoF002
noncomputable section
open IsingBulk.Anisotropic Geometry Set Filter
open scoped Topology

theorem nonextension_on_obstruction_closure {D S : Set ℂ} {f : ℂ → ℂ}
    (hS : ∀ z ∈ S, ¬ HasDomainExtension D f z) {z : ℂ} (hz : z ∈ closure S) :
    ¬ HasDomainExtension D f z := by
  rintro ⟨U, hU, hzU, g, hg, heq⟩
  obtain ⟨w, hwU, hwS⟩ := mem_closure_iff.mp hz U hU hzU
  exact hS w hwS ⟨U, hU, hwU, g, hg, heq⟩

theorem natural_boundary_of_obstruction_closure {D S : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hd : frontier D ⊆ closure S)
    (hS : ∀ z ∈ S, ¬ HasDomainExtension D f z) : NaturalBoundaryOn D f :=
  ⟨hf, fun _ hz => nonextension_on_obstruction_closure hS (hd hz)⟩

theorem literal_high_boundary_of_regular_obstructions {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (omegaH lam))
    (hreg : ∀ z ∈ regularBoundaryF002 lam (omegaH lam),
      ¬ HasDomainExtension (omegaH lam) f z) : NaturalBoundaryOn (omegaH lam) f := by
  apply natural_boundary_of_obstruction_closure hf _ hreg
  rw [literal_high_regular_dense hlam hne]

theorem literal_low_boundary_of_regular_obstructions {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (omegaL lam))
    (hreg : ∀ z ∈ regularBoundaryF002 lam (omegaL lam),
      ¬ HasDomainExtension (omegaL lam) f z) : NaturalBoundaryOn (omegaL lam) f := by
  apply natural_boundary_of_obstruction_closure hf _ hreg
  rw [literal_low_regular_dense hlam hne]

theorem extension_divide_analytic_factor {D : Set ℂ} {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0)
    (he : HasDomainExtension D (b * f) z) : HasDomainExtension D f z := by
  obtain ⟨U, hU, hzU, g, hg, hgf⟩ := he
  have hlocal : ∀ᶠ s in 𝓝 z, AnalyticAt ℂ b s ∧ b s ≠ 0 :=
    hb.eventually_analyticAt.and (hb.continuousAt.eventually_ne hb0)
  obtain ⟨V, hV, hVopen, hzV⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U ∩ V, hU.inter hVopen, ⟨hzU, hzV⟩, (fun s => g s / b s), ?_, ?_⟩
  · intro s hs
    exact (hg s hs.1).div (hV hs.2).1 (hV hs.2).2
  · intro s hs
    dsimp only
    rw [hgf ⟨hs.1.1, hs.2⟩]
    simp only [Pi.mul_apply]
    exact mul_div_cancel_left₀ (f s) (hV hs.1.2).2

theorem natural_boundary_energy_factor {J : ℝ} (hJ : 0 < J)
    {D : Set ℂ} {f : ℂ → ℂ} (hf : NaturalBoundaryOn D f)
    (h0 : ∀ z ∈ frontier D, z ≠ 0) :
    NaturalBoundaryOn D (inverseTemperature J * f) := by
  have hb (z : ℂ) : AnalyticAt ℂ (inverseTemperature J) z :=
    analyticAt_id.div_const
  refine ⟨fun z hz => (hb z).mul (hf.1 z hz), ?_⟩
  intro z hz he
  have hb0 : inverseTemperature J z ≠ 0 := by
    change z / (2 * (J : ℂ)) ≠ 0
    exact div_ne_zero (h0 z hz)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hJ)))
  exact hf.2 z hz (extension_divide_analytic_factor (hb z) hb0 he)

theorem literal_high_energy_boundary {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam)
    {f : ℂ → ℂ} (hf : NaturalBoundaryOn (omegaH lam) f) :
    NaturalBoundaryOn (omegaH lam) (inverseTemperature J * f) :=
  natural_boundary_energy_factor hJ hf (fun _ hz => literal_high_frontier_ne_zero hlam hz)

theorem literal_low_energy_boundary {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam)
    {f : ℂ → ℂ} (hf : NaturalBoundaryOn (omegaL lam) f) :
    NaturalBoundaryOn (omegaL lam) (inverseTemperature J * f) :=
  natural_boundary_energy_factor hJ hf (fun _ hz => literal_low_frontier_ne_zero hlam hz)

end
end IsingBulk.AnisoF002
