import IsingBulk.AnisoF002.C03.NegativeAngularExponentialMoment

/-!
# The pointwise angular power bounds following F002 Lemma 4.2

Every angular direction is retained.  These estimates combine the genuine
maximum `Z_n` with the complete cubic and quartic sums; the already proved
exponential moment controls the exceptional angular directions.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem angular_fourth_power_sum {d : ℕ} (θ : AngularSphere d) :
    (∑ i, (θ.val : Ambient d) i ^ 4) ≤ angularZ θ / ((d + 1 : ℕ) : ℝ) := by
  calc
    _ = ∑ i, ((θ.val : Ambient d) i ^ 2) * ((θ.val : Ambient d) i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, ((θ.val : Ambient d) i ^ 2) * planeMaxSquare θ.val :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (coordinate_sq_le_max θ.val i) (sq_nonneg _))
    _ = planeMaxSquare θ.val := by rw [← Finset.sum_mul, angular_norm_sq, one_mul]
    _ = _ := by unfold angularZ; field_simp

theorem angular_cubic_power_sum {d : ℕ} (θ : AngularSphere d) :
    (∑ i, |(θ.val : Ambient d) i| ^ 3) ≤
      Real.sqrt (angularZ θ) / Real.sqrt ((d + 1 : ℕ) : ℝ) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |(θ.val : Ambient d) i|) (fun i => (θ.val : Ambient d) i ^ 2)
  have he : (∑ i, |(θ.val : Ambient d) i| * (θ.val : Ambient d) i ^ 2) =
      ∑ i, |(θ.val : Ambient d) i| ^ 3 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← sq_abs]
    ring
  rw [he] at hc
  simp only [sq_abs, ← pow_mul, Nat.reduceMul] at hc
  rw [angular_norm_sq, one_mul] at hc
  have hfour := angular_fourth_power_sum θ
  have hnon : 0 ≤ angularZ θ / ((d + 1 : ℕ) : ℝ) :=
    div_nonneg (angularZ_nonneg θ) (by positivity)
  have hs := Real.sq_sqrt hnon
  have hbound : (∑ i, |(θ.val : Ambient d) i| ^ 3) ≤
      Real.sqrt (angularZ θ / ((d + 1 : ℕ) : ℝ)) := by
    nlinarith [Real.sqrt_nonneg (angularZ θ / ((d + 1 : ℕ) : ℝ)),
      Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin (d + 1)))) =>
        pow_nonneg (abs_nonneg ((θ.val : Ambient d) i)) 3)]
  rwa [Real.sqrt_div (angularZ_nonneg θ)] at hbound

/-- With `Q=r^2`, this is exactly `sum v_i^4 <= Q^2 Z_n/n`. -/
theorem angular_scaled_fourth_power_sum {d : ℕ} (θ : AngularSphere d) (r : ℝ) :
    (∑ i, (r * (θ.val : Ambient d) i) ^ 4) ≤
      r ^ 4 * angularZ θ / ((d + 1 : ℕ) : ℝ) := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (angular_fourth_power_sum θ) (by positivity : 0 ≤ r ^ 4)

/-- With `Q=r^2`, this is exactly the full cubic bound `Q^(3/2) sqrt(Z_n)/sqrt(n)`. -/
theorem angular_scaled_cubic_power_sum {d : ℕ} (θ : AngularSphere d) (r : ℝ) :
    (∑ i, |r * (θ.val : Ambient d) i| ^ 3) ≤
      |r| ^ 3 * Real.sqrt (angularZ θ) / Real.sqrt ((d + 1 : ℕ) : ℝ) := by
  simp_rw [abs_mul, mul_pow]
  rw [← Finset.mul_sum]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (angular_cubic_power_sum θ) (pow_nonneg (abs_nonneg r) 3)

end
end IsingBulk.AnisoF002.NegativeHT.Angular
