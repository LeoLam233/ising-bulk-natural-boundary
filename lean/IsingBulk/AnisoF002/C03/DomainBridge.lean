import IsingBulk.AnisoF002.C03.RegularDensity

/-!
# Exact interfaces with the immutable terminal domains

These equalities unfold only the original geometric definitions.  No
historical domain theorem or natural-boundary endpoint is invoked.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set

theorem spectralSetF002_eq_literal (lam : ℝ) :
    spectralSetF002 lam = spectralSet lam := rfl

theorem omegaHF002_eq_literal (lam : ℝ) : omegaHF002 lam = omegaH lam := rfl

theorem omegaLF002_eq_literal (lam : ℝ) : omegaLF002 lam = omegaL lam := rfl

theorem literal_high_frontier {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaH lam) =
      {z : ℂ | |z.im| ≤ sliceY lam ∧ |z.re| = sliceH lam z.im} :=
  frontier_omegaHF002 hlam

theorem literal_low_frontier {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaL lam) = {z : ℂ | sliceL lam z.im = z.re} :=
  frontier_omegaLF002 hlam

theorem literal_high_regular_dense {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    closure (regularBoundaryF002 lam (omegaH lam)) = frontier (omegaH lam) :=
  closure_regular_high_boundary hlam hne

theorem literal_low_regular_dense {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    closure (regularBoundaryF002 lam (omegaL lam)) = frontier (omegaL lam) :=
  closure_regular_low_boundary hlam hne

theorem literal_high_frontier_ne_zero {lam : ℝ}
    (hlam : 0 < lam) {z : ℂ} (hz : z ∈ frontier (omegaH lam)) : z ≠ 0 := by
  intro heq
  subst z
  have h := hz.2
  change (0 : ℂ) ∉ interior (omegaHF002 lam) at h
  rw [(isOpen_omegaHF002 hlam).interior_eq] at h
  exact h (zero_mem_omegaHF002 hlam)

theorem literal_low_frontier_ne_zero {lam : ℝ}
    (hlam : 0 < lam) {z : ℂ} (hz : z ∈ frontier (omegaL lam)) : z ≠ 0 := by
  intro heq
  subst z
  have h : lowProfileF002 lam 0 = 0 := by
    change (0 : ℂ) ∈ frontier (omegaLF002 lam) at hz
    simpa only [frontier_omegaLF002 hlam, Set.mem_ofPred_eq, Complex.zero_re,
      Complex.zero_im] using hz
  have hpos : 0 < lowProfileF002 lam 0 := by
    rw [lowProfileF002]
    simp only [Real.cos_zero, mul_zero, abs_one]
    exact lt_of_lt_of_le (criticalPointF002_pos hlam) (le_max_left _ _)
  linarith

end
end IsingBulk.AnisoF002.Geometry
