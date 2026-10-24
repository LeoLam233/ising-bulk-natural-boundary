import IsingBulk.Anisotropic.RegularEdges.HorizontalAngularSum

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open FormFactors IsingBulk.First IsingBulk.HT.Contour

/-- The actual anisotropic N−1-angle coefficient equals the whole lattice sum.
Both independent lattice directions are summed absolutely before inversion. -/
theorem angularCoefficient_eq_lattice_tsum (n : ℕ) {lam x : ℝ}
    (hlam : 0<lam) (hx : 0<x) (hp : realProduct lam x≠1) :
    angularCoefficient n (realB lam x) (realC lam x) =
      ∑' v : LatticeSite, latticeCoefficient (n+1) (realB lam x) (realC lam x) v := by
  have hB := realB_pos hlam hx
  have hgap := real_dispersion_gap hlam hx hp
  have hs := (physical_lattice_summable_eq_full (n+1) (by omega) hlam hx hp).1.of_norm
  symm
  rw [hs.tsum_prod]
  calc
    (∑' m : ℤ, ∑' k : ℤ, latticeCoefficient (n+1) (realB lam x) (realC lam x) (m,k)) =
      ∑' m : ℤ, anisotropicConstrainedVerticalCoefficient n (realB lam x) (realC lam x) m.natAbs := by
      apply tsum_congr
      intro m
      have he : (fun k : ℤ => latticeCoefficient (n+1) (realB lam x) (realC lam x) (m,k)) =
          (fun k : ℤ => latticeCoefficient (n+1) (realB lam x) (realC lam x) ((m.natAbs:ℤ),k)) := by
        funext k
        simp only [latticeCoefficient,Int.natAbs_natCast]
      rw [he]
      exact anisotropic_horizontal_tsum n m.natAbs hB hgap hs
    _ = angularCoefficient n (realB lam x) (realC lam x) :=
      (anisotropicConstrainedVerticalCoefficient_summable_eq_angular n hB.le hgap).2

theorem scaled_unscaledFullCoefficient_eq_angular (n : ℕ) {lam x : ℝ}
    (hlam : 0<lam) (hx : 0<x) (hp : realProduct lam x≠1) :
    ((Real.sqrt (realProduct lam x))^(n+1):ℝ)*unscaledFullCoefficient (n+1) lam (x:ℂ) =
      angularCoefficient n (realB lam x) (realC lam x) := by
  rw [angularCoefficient_eq_lattice_tsum n hlam hx hp]
  exact (physical_lattice_summable_eq_full (n+1) (by omega) hlam hx hp).2.symm

end
end IsingBulk.Anisotropic.RegularEdges
