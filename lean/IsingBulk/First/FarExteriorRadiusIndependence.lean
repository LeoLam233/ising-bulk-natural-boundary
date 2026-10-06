import IsingBulk.First.FarExteriorMixedContour

/-! Genuine actual-source annulus transport for the near-infinity symmetry
germ. No boundary-uniform sum or TAIL assertion is made. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

theorem farExterior_mixedDoubleFormFactor_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hs : 16 < ‖s‖) :
    mixedDoubleFormFactor N R ry s = mixedDoubleFormFactor N r ry s := by
  unfold mixedDoubleFormFactor
  congr 1
  apply multiCircleIntegral_congr ((show 0 < r by linarith).trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := by
    intro i
    rw [hyc i]
    exact hy
  exact multiCircleIntegral_radius_eq N (show 0 < r by linarith) hrR _ (farExterior_doubleDensity_x_annular N hN hr hR hs y hyb)

/-- All coordinate contours move through the actual pole-free annular region.
The argument uses genuine Fubini when exchanging the x and y groups. -/
theorem farExterior_doubleFormFactor_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hs : 16 < ‖s‖) : doubleFormFactor N R s = doubleFormFactor N r s := by
  change mixedDoubleFormFactor N R R s = mixedDoubleFormFactor N r r s
  calc
    _ = mixedDoubleFormFactor N r R s :=
      farExterior_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨hrR, le_rfl⟩ hs
    _ = mixedDoubleFormFactor N R r s :=
      farExterior_mixedDoubleFormFactor_swap N hN hr hR ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩ hs
    _ = _ := farExterior_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨le_rfl, hrR⟩ hs

end
end IsingBulk.First
