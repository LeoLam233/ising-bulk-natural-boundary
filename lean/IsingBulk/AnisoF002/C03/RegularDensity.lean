import IsingBulk.AnisoF002.Geometry.ProfileIntersections

/-!
# Density on the complete physical frontiers

F002 proposition 2.4, the density step, including both finite HT tips and
all LT contacts.  The actual analytic profile difference controls the
exceptional heights.  These are density statements for the actual
frontiers; they do not assert the particle singularity mechanisms.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set Filter
open scoped Topology

theorem profileDifference_nonzero_dense {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    Dense {y : ℝ | profileDifferenceF002 lam y ≠ 0} := by
  intro y
  exact ((profileDifference_locally_nonzero hlam hne y).frequently.filter_mono
    nhdsWithin_le_nhds).mem_closure

/-- The two factors do not vanish together and the real part is nonzero.
The endpoint coordinate and side theorems attach to these points. -/
def regularBoundaryF002 (lam : ℝ) (D : Set ℂ) : Set ℂ :=
  {z | z ∈ frontier D ∧ z.re ≠ 0 ∧ profileDifferenceF002 lam z.im ≠ 0}

theorem regularBoundaryF002_factors {lam : ℝ} {D : Set ℂ} {z : ℂ}
    (hlam : 0 < lam) (hD : frontier D ⊆ endpointLocusF002 lam)
    (hz : z ∈ regularBoundaryF002 lam D) :
    (geometryF1 lam z.re z.im = 0 ∧ geometryF2 lam z.re z.im ≠ 0) ∨
      (geometryF2 lam z.re z.im = 0 ∧ geometryF1 lam z.re z.im ≠ 0) :=
  endpoint_locus_regular_factors hlam (hD hz.1) hz.2.2

theorem closure_regular_low_boundary {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    closure (regularBoundaryF002 lam (omegaLF002 lam)) = frontier (omegaLF002 lam) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) isClosed_frontier
  · intro z hz
    have hz' : lowProfileF002 lam z.im = z.re := by
      simpa only [frontier_omegaLF002 hlam, Set.mem_ofPred_eq] using hz
    let g : ℝ → ℂ := fun y => (lowProfileF002 lam y : ℂ) + (y : ℂ) * Complex.I
    have hg : Continuous g := by
      unfold g
      exact ((Complex.continuous_ofReal.comp (lowProfile_continuous hlam))).add
        (Complex.continuous_ofReal.mul continuous_const)
    have himage := mem_closure_image hg.continuousAt
      (profileDifference_nonzero_dense hlam hne z.im)
    have hsub : g '' {y : ℝ | profileDifferenceF002 lam y ≠ 0} ⊆
        regularBoundaryF002 lam (omegaLF002 lam) := by
      rintro w ⟨y, hy, rfl⟩
      have hpos := lowProfile_pos_of_difference_ne_zero hlam hy
      refine ⟨?_, ?_, ?_⟩
      · rw [frontier_omegaLF002 hlam]
        simp [g]
      · simpa [g] using ne_of_gt hpos
      · simpa [g] using hy
    have hh := closure_mono hsub himage
    have hg_eq : g z.im = z := by
      apply Complex.ext <;> simp [g, hz']
    rwa [hg_eq] at hh

theorem profile_regular_heights_closure {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    Icc (-highStripWidthF002 lam) (highStripWidthF002 lam) ⊆
      closure (Ioo (-highStripWidthF002 lam) (highStripWidthF002 lam) ∩
        {y : ℝ | profileDifferenceF002 lam y ≠ 0}) := by
  have hY := (highStripWidth_bounds hlam).1
  have hs := (profileDifference_nonzero_dense hlam hne).open_subset_closure_inter
    (isOpen_Ioo : IsOpen (Ioo (-highStripWidthF002 lam) (highStripWidthF002 lam)))
  have hc := closure_mono hs
  rw [closure_closure, closure_Ioo (by linarith :
    -highStripWidthF002 lam ≠ highStripWidthF002 lam)] at hc
  exact hc

theorem high_boundary_graph_mem_closure_regular {lam e y : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) (he : e = 1 ∨ e = -1)
    (hy : |y| ≤ highStripWidthF002 lam) :
    ((e * highProfileF002 lam y : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
      closure (regularBoundaryF002 lam (omegaHF002 lam)) := by
  let g : ℝ → ℂ := fun t => ((e * highProfileF002 lam t : ℝ) : ℂ) +
    (t : ℂ) * Complex.I
  have hg : Continuous g := by
    unfold g
    exact (Complex.continuous_ofReal.comp
      (continuous_const.mul (highProfile_continuous hlam))).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hheight := profile_regular_heights_closure hlam hne (abs_le.mp hy)
  have himage := mem_closure_image hg.continuousAt hheight
  have hsub : g '' (Ioo (-highStripWidthF002 lam) (highStripWidthF002 lam) ∩
      {t : ℝ | profileDifferenceF002 lam t ≠ 0}) ⊆
      regularBoundaryF002 lam (omegaHF002 lam) := by
    rintro w ⟨t, ⟨ht, hE⟩, rfl⟩
    have ht' : |t| < highStripWidthF002 lam := abs_lt.mpr ht
    have hp := highProfile_pos hlam ht'
    have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
    have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    refine ⟨?_, ?_, ?_⟩
    · rw [frontier_omegaHF002 hlam]
      change |(g t).im| ≤ highStripWidthF002 lam ∧
        |(g t).re| = highProfileF002 lam (g t).im
      simpa [g, abs_mul, heabs, abs_of_pos hp] using ht'.le
    · simpa [g] using mul_ne_zero he0 (ne_of_gt hp)
    · simpa [g] using hE
  exact closure_mono hsub himage

theorem closure_regular_high_boundary {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    closure (regularBoundaryF002 lam (omegaHF002 lam)) = frontier (omegaHF002 lam) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) isClosed_frontier
  · intro z hz
    have hz' : |z.im| ≤ highStripWidthF002 lam ∧
        |z.re| = highProfileF002 lam z.im := by
      simpa only [frontier_omegaHF002 hlam, Set.mem_ofPred_eq] using hz
    by_cases hx : 0 ≤ z.re
    · have h := high_boundary_graph_mem_closure_regular hlam hne (Or.inl rfl) hz'.1
      have heq : (((1 : ℝ) * highProfileF002 lam z.im : ℝ) : ℂ) +
          (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [← hz'.2, abs_of_nonneg hx]
      rwa [heq] at h
    · have h := high_boundary_graph_mem_closure_regular hlam hne (Or.inr rfl) hz'.1
      have heq : (((-1 : ℝ) * highProfileF002 lam z.im : ℝ) : ℂ) +
          (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [← hz'.2, abs_of_neg (lt_of_not_ge hx)]
      rwa [heq] at h

end
end IsingBulk.AnisoF002.Geometry
