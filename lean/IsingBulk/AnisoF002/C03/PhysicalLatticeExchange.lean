import IsingBulk.AnisoF002.C03.PhysicalLatticeIntegral
import IsingBulk.AnisoF002.C03.PhysicalContourRadius
import IsingBulk.AnisoF002.C03.PhysicalRealFactors
import IsingBulk.AnisoF002.C03.PhysicalPrefactors

/-!
# Actual particle/lattice exchange following finite physical residues

The finite coefficient identity is the explicit mathematical input to this
exchange step.  Joint all-site/all-particle summability is derived from the
literal contour; it is not an added physical premise.  The finite residue
construction supplies this identity in the subsequent attachment module.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry
open scoped BigOperators

theorem literal_real_lattice_sum {N : ℕ} (hN : 0 < N) {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ v : LatticeSite, latticeCoefficient N (realB lam x) (realC lam x) v =
      (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v) :
    (∑' v : LatticeSite, latticeCoefficient N (realB lam x) (realC lam x) v) =
      (Real.sqrt (realProduct lam x) : ℂ) ^ N * unscaledFullCoefficient N lam (x : ℂ) := by
  simp_rw [hrep]
  rw [tsum_mul_left, literal_latticeCoefficient_tsum hN ha,
    ← literal_chosenCoefficient_eq_fixed hN (positive_real_not_mem_spectralSetF002 hlam hx hp) ha]

theorem literal_real_joint_summable {lam x r : ℝ}
    (ha : ContourAnnulus lam (x : ℂ) r) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hinj : Function.Injective N)
    (hrep : ∀ n (v : LatticeSite), latticeCoefficient (N n) (realB lam x) (realC lam x) v =
      (Real.sqrt (realProduct lam x) : ℂ) ^ N n * literalLatticeCoefficientAtRadius (N n) r lam (x : ℂ) v) :
    Summable (fun nv : ℕ × LatticeSite => latticeCoefficient (N nv.1) (realB lam x) (realC lam x) nv.2) := by
  apply (literal_lattice_joint_summable (a := (Real.sqrt (realProduct lam x) : ℂ)) ha N hN hinj).congr
  intro nv
  exact (hrep nv.1 nv.2).symm

theorem literal_real_lattice_exchange {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (ha : ContourAnnulus lam (x : ℂ) r) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hinj : Function.Injective N)
    (hrep : ∀ n (v : LatticeSite), latticeCoefficient (N n) (realB lam x) (realC lam x) v =
      (Real.sqrt (realProduct lam x) : ℂ) ^ N n * literalLatticeCoefficientAtRadius (N n) r lam (x : ℂ) v) :
    Summable (fun v : LatticeSite => ∑' n, latticeCoefficient (N n) (realB lam x) (realC lam x) v) ∧
      (∑' v : LatticeSite, ∑' n, latticeCoefficient (N n) (realB lam x) (realC lam x) v) =
        ∑' n, (Real.sqrt (realProduct lam x) : ℂ) ^ N n * unscaledFullCoefficient (N n) lam (x : ℂ) := by
  have hs := literal_real_joint_summable ha N hN hinj hrep
  refine ⟨hs.prod_symm.prod, ?_⟩
  rw [Summable.tsum_comm (f := fun n v => latticeCoefficient (N n) (realB lam x) (realC lam x) v) hs]
  exact tsum_congr fun n => literal_real_lattice_sum (hN n) hlam hx hp ha (hrep n)

theorem literal_real_root_odd_power {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (n : ℕ) :
    (Real.sqrt (realProduct lam x) : ℂ) ^ (2 * n + 1) =
      (Real.sqrt (realProduct lam x) : ℂ) * spectralProduct lam (x : ℂ) ^ n := by
  have hp := (Physical.realProduct_pos hlam hx).le
  rw [Physical.spectralProduct_real, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [pow_succ, pow_mul, Real.sq_sqrt hp, mul_comm]

theorem literal_real_root_even_power {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (n : ℕ) :
    (Real.sqrt (realProduct lam x) : ℂ) ^ (2 * n + 2) = spectralProduct lam (x : ℂ) ^ (n + 1) := by
  have hp := (Physical.realProduct_pos hlam hx).le
  rw [Physical.spectralProduct_real, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  congr 1
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul, Real.sq_sqrt hp]

theorem literal_real_oddSiteSeries {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
      latticeCoefficient N (realB lam x) (realC lam x) v =
        (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v) :
    Summable (oddSiteSeries lam x) ∧
      (∑' v, oddSiteSeries lam x v) = (Real.sqrt (realProduct lam x) : ℂ) *
        ∑' n, spectralProduct lam (x : ℂ) ^ n * unscaledFullCoefficient (2 * n + 1) lam (x : ℂ) := by
  have hs := literal_real_lattice_exchange hlam hx hp ha (fun n => 2 * n + 1)
    (fun _ => by omega) (fun n m hnm => by dsimp only at hnm; omega) (fun n v => hrep _ (by omega) v)
  refine ⟨hs.1, ?_⟩
  change (∑' v, ∑' n, latticeCoefficient (2 * n + 1) (realB lam x) (realC lam x) v) = _
  rw [hs.2]
  simp_rw [literal_real_root_odd_power hlam hx, mul_assoc]
  rw [tsum_mul_left]

theorem literal_real_evenSiteSeries {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
      latticeCoefficient N (realB lam x) (realC lam x) v =
        (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v) :
    Summable (evenSiteSeries lam x) ∧
      (∑' v, evenSiteSeries lam x v) =
        ∑' n, spectralProduct lam (x : ℂ) ^ (n + 1) * unscaledFullCoefficient (2 * n + 2) lam (x : ℂ) := by
  have hs := literal_real_lattice_exchange hlam hx hp ha (fun n => 2 * n + 2)
    (fun _ => by omega) (fun n m hnm => by dsimp only at hnm; omega) (fun n v => hrep _ (by omega) v)
  refine ⟨hs.1, ?_⟩
  change (∑' v, ∑' n, latticeCoefficient (2 * n + 2) (realB lam x) (realC lam x) v) = _
  rw [hs.2]
  exact tsum_congr fun n => congrArg (fun t => t * unscaledFullCoefficient (2 * n + 2) lam (x : ℂ))
    (literal_real_root_even_power hlam hx n)

end
end IsingBulk.AnisoF002.RegularTail.C03
