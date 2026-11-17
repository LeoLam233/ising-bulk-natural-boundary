import IsingBulk.AnisoF002.C03.PhysicalLatticeDefinitions
import IsingBulk.AnisoF002.C03.PhysicalContourBound
import IsingBulk.AnisoF002.C03.PhysicalHadamardSummability
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Absolute all-site and all-particle convergence on one actual contour

Both lattice displacement signs and both coordinate axes are included.
The same fixed radius precedes every site and every particle number.
No physical summability assertion is assumed.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open scoped BigOperators Topology

theorem literal_integer_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℤ => r ^ m.natAbs) := by
  have hs := summable_geometric_of_lt_one hr hr1
  apply Summable.of_nat_of_neg_add_one
  · simpa only [Int.natAbs_natCast] using hs
  · have hs' : Summable (fun n : ℕ => r ^ (n + 1)) := hs.comp_injective Nat.succ_injective
    convert hs' using 1
    funext n
    congr 1

def literalSiteEnvelope (r : ℝ) (v : LatticeSite) : ℝ :=
  r ^ v.1.natAbs * r ^ v.2.natAbs

theorem literalSiteEnvelope_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (literalSiteEnvelope r) :=
  (literal_integer_geometric_summable hr hr1).mul_of_nonneg
    (literal_integer_geometric_summable hr hr1) (fun _ => pow_nonneg hr _) (fun _ => pow_nonneg hr _)

theorem literal_onsiteDensity_bound {N : ℕ} {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = r) (hy : ∀ i, ‖y i‖ = r)
    (hA : ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤ A) :
    ‖onsiteDensity lam z x y‖ ≤ (r ^ N)⁻¹ * (r ^ N)⁻¹ * A * M ^ N := by
  have hX : ‖coordinateProduct x‖ = r ^ N := by simp [coordinateProduct, norm_prod, hx]
  have hY : ‖coordinateProduct y‖ = r ^ N := by simp [coordinateProduct, norm_prod, hy]
  have hMprod : ‖∏ i, (sliceDispersion lam z (x i) (y i))⁻¹‖ ≤ M ^ N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hD _ _ (hx i) (hy i))
      _ = _ := by simp
  have hA0 : 0 ≤ A := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hA
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul hA hMprod (norm_nonneg _) hA0)
    (by positivity : 0 ≤ (r ^ N)⁻¹ * (r ^ N)⁻¹)
  unfold FormFactors.onsiteDensity FormFactors.commonDensity
  simp only [norm_mul, norm_inv, hX, hY, mul_inv_rev]
  nlinarith only [hh]

theorem literal_latticeDensity_bound {N : ℕ} {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (v : LatticeSite) (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = r) (hy : ∀ i, ‖y i‖ = r)
    (hA : ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤ A) :
    ‖literalLatticeDensity lam z v x y‖ ≤
      r ^ (N * v.1.natAbs) * r ^ (N * v.2.natAbs) *
        ((r ^ N)⁻¹ * (r ^ N)⁻¹ * A * M ^ N) := by
  have hX : ‖coordinateProduct x‖ = r ^ N := by simp [coordinateProduct, norm_prod, hx]
  have hY : ‖coordinateProduct y‖ = r ^ N := by simp [coordinateProduct, norm_prod, hy]
  unfold literalLatticeDensity
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hX, hY, ← pow_mul, ← pow_mul]
  exact mul_le_mul_of_nonneg_left (literal_onsiteDensity_bound hr hD x y hx hy hA) (by positivity)

theorem literal_latticeCoefficient_bound {N : ℕ} {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (hA : ∀ x y : Fin N → ℂ, (∀ i, ‖x i‖ = r) → (∀ i, ‖y i‖ = r) →
      ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤ A) (v : LatticeSite) :
    ‖literalLatticeCoefficientAtRadius N r lam z v‖ ≤
      r ^ (N * v.1.natAbs) * r ^ (N * v.2.natAbs) * (A * M ^ N / (N.factorial : ℝ)) := by
  have hinner (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖ = r) :=
    literal_multiCircleIntegral_norm_le N hr.le (fun x => literalLatticeDensity lam z v x y)
      (fun x hx => literal_latticeDensity_bound hr hD v x y hx hy (hA x y hx hy))
  have hout := literal_multiCircleIntegral_norm_le N hr.le
    (fun y => multiCircleIntegral r N (fun x => literalLatticeDensity lam z v x y))
    (fun y hy => hinner y hy)
  have hh := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ (N.factorial : ℝ)⁻¹)
  unfold literalLatticeCoefficientAtRadius
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert hh using 1
  field_simp

theorem literal_latticeCoefficient_envelope {N : ℕ} (hN : 0 < N)
    {lam r M : ℝ} {z : ℂ} (hr : 0 < r) (hr1 : r < 1) (hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (v : LatticeSite) :
    ‖literalLatticeCoefficientAtRadius N r lam z v‖ ≤
      (literalContourKernelBound r * literalHadamardEnvelope (literalContourPairBound r * M) N) *
        literalSiteEnvelope r v := by
  have hh := literal_latticeCoefficient_bound hr hD
    (fun x y hx hy => literal_circle_pairProduct_bound N hN hr hr1 x y hx hy) v
  have hm (m : ℕ) : r ^ (N * m) ≤ r ^ m := by
    apply pow_le_pow_of_le_one hr.le hr1.le
    simpa only [one_mul] using Nat.mul_le_mul_right m (show 1 ≤ N by omega)
  have hp := mul_le_mul (hm v.1.natAbs) (hm v.2.natAbs) (by positivity) (by positivity)
  have hC := literalContourKernelBound_ge_one hr.le hr1
  have hk : 0 ≤ literalContourPairBound r := by unfold literalContourPairBound; positivity
  have hb := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ (literalContourKernelBound r * literalContourPairBound r ^ N *
      (N : ℝ) ^ (N - N / 2)) * M ^ N / (N.factorial : ℝ))
  exact hh.trans (by
    convert hb using 1
    unfold literalHadamardEnvelope literalSiteEnvelope
    rw [mul_pow]
    ring)

theorem literal_lattice_joint_summable {lam r : ℝ} {z a : ℂ}
    (ha : ContourAnnulus lam z r) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hinj : Function.Injective N) :
    Summable (fun nv : ℕ × LatticeSite =>
      a ^ N nv.1 * literalLatticeCoefficientAtRadius (N nv.1) r lam z nv.2) := by
  obtain ⟨M, hM, he⟩ := literal_local_inverse_dispersion_bound ha
  have hD := he.self_of_nhds
  let C := literalContourPairBound r * M
  have hr : 0 < r := ha.1
  have hK := literalContourKernelBound_ge_one ha.1.le ha.2.1
  have hC : 0 ≤ C := by dsimp [C, literalContourPairBound]; positivity
  have hnum : Summable (fun n => literalContourKernelBound r *
      literalHadamardEnvelope (C * ‖a‖) (N n)) :=
    ((literalHadamardEnvelope_summable (mul_nonneg hC (norm_nonneg a))).comp_injective hinj).mul_left
      (literalContourKernelBound r)
  have hsite := literalSiteEnvelope_summable ha.1.le ha.2.1
  apply (hnum.mul_of_nonneg hsite (fun n => by unfold literalHadamardEnvelope; positivity)
    (fun v => by unfold literalSiteEnvelope; positivity)).of_norm_bounded
  intro nv
  have hh := mul_le_mul_of_nonneg_left
    (literal_latticeCoefficient_envelope (hN nv.1) ha.1 ha.2.1 hM.le hD nv.2)
    (pow_nonneg (norm_nonneg a) (N nv.1))
  rw [norm_mul, norm_pow]
  convert hh using 1
  dsimp only [literalHadamardEnvelope, C]
  simp only [mul_pow]
  ring

end
end IsingBulk.AnisoF002.RegularTail.C03
