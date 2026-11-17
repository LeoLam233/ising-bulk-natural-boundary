import IsingBulk.AnisoF002.C03.NegativeDensityLogBounds
import IsingBulk.AnisoF002.C03.NegativeGaussianMehta

/-!
# A complete Vandermonde ball bound for every particle order

Applying the arithmetic-geometric mean inequality to all unordered pairs
gives the required `exp(-N² log N / 2 + O(N²))` scale directly.  The bound
uses the literal independent-coordinate measure and does not require a
convergent beta integral or a restriction on the Taylor order.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

theorem full_product_le_of_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hsum : ∑ i ∈ s, f i ≤ (s.card : ℝ) * a) :
    ∏ i ∈ s, f i ≤ a ^ s.card := by
  have hpoint : ∀ i ∈ s, f i ≤ a * Real.exp (f i / a - 1) := by
    intro i _
    have hh := Real.add_one_le_exp (f i / a - 1)
    have hd : f i / a ≤ Real.exp (f i / a - 1) := by linarith
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hd
  have hexp : (∑ i ∈ s, (f i / a - 1)) ≤ 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hh := (div_le_iff₀ ha).mpr hsum
    linarith
  calc
    _ ≤ ∏ i ∈ s, a * Real.exp (f i / a - 1) := Finset.prod_le_prod₀ hf hpoint
    _ = a ^ s.card * Real.exp (∑ i ∈ s, (f i / a - 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    _ ≤ a ^ s.card * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hexp) (pow_nonneg ha.le _)
    _ = _ := mul_one _

theorem sum_pair_difference_sq_le {d : ℕ} (v : constrainedPlane d) :
    (∑ ij ∈ indexPairs (d + 1),
      ((v : Ambient d) ij.1 - (v : Ambient d) ij.2) ^ 2) ≤
      4 * ((d + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  have hp : (∑ ij ∈ indexPairs (d + 1),
      ((v : Ambient d) ij.1 - (v : Ambient d) ij.2) ^ 2) ≤
      2 * ∑ ij ∈ indexPairs (d + 1),
        (((v : Ambient d) ij.1) ^ 2 + ((v : Ambient d) ij.2) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ij _
    nlinarith [sq_nonneg ((v : Ambient d) ij.1 + (v : Ambient d) ij.2)]
  have hs := sum_indexPairs_add_le (fun i => ((v : Ambient d) i) ^ 2)
    (fun i => sq_nonneg _)
  rw [← constrained_norm_sq] at hs
  nlinarith

theorem planeVandermonde_ball_bound {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (v : constrainedPlane d) (hv : ‖v‖ ≤ R) :
    planeVandermonde v ≤ (8 * R ^ 2 / (d : ℝ)) ^ (d + 1).choose 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < 8 * R ^ 2 / (d : ℝ) := by positivity
  have hcard : ((indexPairs (d + 1)).card : ℝ) * (8 * R ^ 2 / (d : ℝ)) =
      4 * ((d + 1 : ℕ) : ℝ) * R ^ 2 := by
    rw [card_indexPairs, Nat.cast_choose_two]
    push_cast
    field_simp
    ring
  have hs : (∑ ij ∈ indexPairs (d + 1),
      ((v : Ambient d) ij.1 - (v : Ambient d) ij.2) ^ 2) ≤
      ((indexPairs (d + 1)).card : ℝ) * (8 * R ^ 2 / (d : ℝ)) := by
    rw [hcard]
    apply (sum_pair_difference_sq_le v).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [norm_nonneg v]
  simpa only [planeVandermonde, RegularTail.vandermondeSquared, card_indexPairs] using
    full_product_le_of_sum_le (indexPairs (d + 1))
      (fun ij => ((v : Ambient d) ij.1 - (v : Ambient d) ij.2) ^ 2)
      ha (fun ij _ => sq_nonneg _) hs

theorem independentMeasure_closedBall_bound (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (independentMeasure d).real (Metric.closedBall (0 : constrainedPlane d) R) ≤ (2 * R) ^ d := by
  have hsub : (independentChart d) ⁻¹' Metric.closedBall (0 : constrainedPlane d) R ⊆
      Icc (fun _ : Fin d => -R) (fun _ => R) := by
    intro x hx
    have hxR : ‖independentChart d x‖ ≤ R := by
      simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hx
    have hb (i : Fin d) : (x i) ^ 2 ≤ ‖independentChart d x‖ ^ 2 := by
      rw [constrained_norm_sq]
      have hh := RegularTail.coordinate_square_le_sum
        (fun j => (independentChart d x : Ambient d) j) i.castSucc
      simpa only [independentChart_castSucc] using hh
    constructor <;> intro i <;> have hh := hb i <;>
      nlinarith [norm_nonneg (independentChart d x)]
  have hvol : volume.real (Icc (fun _ : Fin d => -R) (fun _ => R)) = (2 * R) ^ d := by
    change (volume (Icc (fun _ : Fin d => -R) (fun _ => R))).toReal = _
    rw [Real.volume_Icc_pi_toReal (by intro i; dsimp; linarith)]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm : Measurable (independentChart d) :=
    (independentChart d).toContinuousLinearEquiv.continuous.measurable
  rw [independentMeasure, Measure.real, Measure.map_apply hm measurableSet_closedBall]
  have hfin : volume (Icc (fun _ : Fin d => -R) (fun _ => R)) ≠ ⊤ :=
    (isCompact_Icc : IsCompact (Icc (fun _ : Fin d => -R) (fun _ => R))).measure_lt_top.ne
  exact (measureReal_mono hsub hfin).trans_eq hvol

theorem full_vandermonde_ball_integral_bound {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    (∫ v in Metric.closedBall (0 : constrainedPlane d) R,
      planeVandermonde v ∂independentMeasure d) ≤
      (2 * R) ^ d * (8 * R ^ 2 / (d : ℝ)) ^ (d + 1).choose 2 := by
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := independentMeasure d) (f := planeVandermonde)
    (isCompact_closedBall (0 : constrainedPlane d) R).measure_lt_top
      (fun v hv => by
        rw [Real.norm_of_nonneg (planeVandermonde_nonneg v)]
        exact planeVandermonde_ball_bound hd hR v
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
  apply (le_abs_self _).trans
  apply hb.trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (independentMeasure_closedBall_bound d hR.le)
    (pow_nonneg (by positivity : 0 ≤ 8 * R ^ 2 / (d : ℝ)) ((d + 1).choose 2))

end
end IsingBulk.AnisoF002.NegativeHT.Angular
