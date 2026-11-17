import IsingBulk.AnisoF002.C03.PhysicalLatticeAngular

/-!
# Actual finite physical lattice identification, all N and all sites

This discharges the finite cut used by the full real-lattice exchange:
one actual contour radius serves every positive particle number and every
integer pair of displacements, retaining both Fourier signs and onsite.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
open scoped BigOperators

theorem literal_latticeCoefficient_natAbs_second (N : ℕ) (B C : ℝ) (m k : ℤ) :
    latticeCoefficient N B C (m, (k.natAbs : ℤ)) = latticeCoefficient N B C (m, k) := by
  by_cases hk : 0 ≤ k
  · rw [Int.natCast_natAbs, abs_of_nonneg hk]
  · rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hk)]
    exact literal_latticeCoefficient_reflect_second N B C m k

theorem literal_finite_lattice_identity {N : ℕ} {lam t r q : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hp : realProduct lam t ≠ 1)
    (hr : ContourAnnulus lam (t : ℂ) r) (hqr : q < r)
    (hroot : ∀ y : ℂ, r ≤ ‖y‖ → ‖y‖ ≤ 1 →
      AnalyticAt ℂ (physicalAnnularRoot (realB lam t) (realC lam t)) y ∧
      physicalAnnularRoot (realB lam t) (realC lam t) y ≠ 0 ∧
      ‖physicalAnnularRoot (realB lam t) (realC lam t) y‖ < q ∧
      physicalAnnularRoot (realB lam t) (realC lam t) y ^ 2 -
        2 * physicalAnnularW (realB lam t) (realC lam t) y *
          physicalAnnularRoot (realB lam t) (realC lam t) y + 1 = 0)
    (v : LatticeSite) :
    latticeCoefficient N (realB lam t) (realC lam t) v =
      (Real.sqrt (realProduct lam t) : ℂ) ^ N *
        literalLatticeCoefficientAtRadius N r lam (t : ℂ) v := by
  rw [← literal_latticeCoefficient_natAbs_second N (realB lam t) (realC lam t) v.1 v.2]
  symm
  rw [literal_lattice_coefficient_eq_filled_unit ht hr hqr hroot v,
    multiCircleIntegral_eq_angle]
  let f : (Fin N → ℝ) → ℂ := fun θ => angleProductJacobian 1 θ *
    latticeFilledResidue (realB lam t : ℂ) (Real.sinh t : ℂ) v
      (fun i => physicalAnnularRoot (realB lam t) (realC lam t) (angleTuple 1 θ i))
      (angleTuple 1 θ)
  let g : (Fin N → ℝ) → ℂ := fun θ =>
    ((angularWeight (realB lam t) (realC lam t) θ *
      rootProduct (realB lam t) (realC lam t) θ ^ v.1.natAbs : ℝ) : ℂ) *
      Complex.exp (Complex.I * (v.2.natAbs : ℂ) * ∑ i, (θ i : ℂ))
  have he : (fun θ => (Real.sqrt (realProduct lam t) : ℂ) ^ N * f θ) =
      fun θ => ((2 * (Real.pi : ℂ))⁻¹) ^ N * g θ := by
    funext θ
    exact filled_unit_angular_integrand hlam ht hp v θ
  calc
    _ = (N.factorial : ℂ)⁻¹ *
        multiAngleIntegral N (fun θ => (Real.sqrt (realProduct lam t) : ℂ) ^ N * f θ) := by
      rw [multiAngleIntegral_const_mul_f002]
      ring
    _ = (N.factorial : ℂ)⁻¹ * ((2 * (Real.pi : ℂ))⁻¹) ^ N * multiAngleIntegral N g := by
      rw [he, multiAngleIntegral_const_mul_f002]
      ring
    _ = _ := by
      simp only [latticeCoefficient, Int.cast_natCast, g]

/-- The finite identity is constructed from the literal positive real
physical parameters.  Its radius is chosen before N and every v in ℤ². -/
theorem exists_physical_finite_lattice_identity {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hp : realProduct lam t ≠ 1) :
    ∃ r : ℝ, ContourAnnulus lam (t : ℂ) r ∧
      ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
        latticeCoefficient N (realB lam t) (realC lam t) v =
          (Real.sqrt (realProduct lam t) : ℂ) ^ N *
            literalLatticeCoefficientAtRadius N r lam (t : ℂ) v := by
  obtain ⟨r, q, hr, _, hqr, hroot⟩ := exists_physical_root_contour hlam ht hp
  exact ⟨r, hr, fun _ _ v => literal_finite_lattice_identity hlam ht hp hr hqr hroot v⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
