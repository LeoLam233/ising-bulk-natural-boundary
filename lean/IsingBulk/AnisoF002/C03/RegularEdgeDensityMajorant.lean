import IsingBulk.AnisoF002.C03.RegularEdgeCompleteControl
import IsingBulk.AnisoF002.C03.RegularCollisionIntegral

/-!
# A summable fixed-block majorant for every complete density derivative

The bound now contains the actual numerator and rational site factor.
All particle indices of either complementary parity are included.  The
angular factor is the proved integrable m-dimensional collision majorant;
the scalar factor is summable after every fixed polynomial loss.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology BigOperators

theorem summable_weighted_affine {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (j k : ℕ)
    (hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (k + j) * f n)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * (L + B * n) ^ j * f n) := by
  have hs' := hs.mul_left ((L + B) ^ j)
  apply Summable.of_nonneg_of_le (fun n => by have hfn := hf n; positivity) _ hs'
  intro n
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hp : (L + B * (n : ℝ)) ^ j ≤ (L + B) ^ j * ((n : ℝ) + 1) ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) j
  calc
    ((n : ℝ) + 1) ^ k * (L + B * n) ^ j * f n ≤
        ((n : ℝ) + 1) ^ k * ((L + B) ^ j * ((n : ℝ) + 1) ^ j) * f n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (hf n)
    _ = (L + B) ^ j * (((n : ℝ) + 1) ^ (k + j) * f n) := by rw [pow_add]; ring

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

def densityJetConstant (j : ℕ) : ℝ := 8 * (j.factorial : ℝ) / d.phase.siteScale ^ j

theorem densityJetConstant_pos (j : ℕ) : 0 < d.densityJetConstant j :=
  div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.factorial_pos j)))
    (pow_pos d.phase.siteScale_pos j)

def retainedEvenEnvelope (m n : ℕ) : ℝ :=
  ((d.numerator.prefactorBound * d.numerator.bodyBound) ^ m * d.numerator.pairBound ^ m.choose 2) *
    evenMatchedBound ((d.numerator.prefactorBound * d.numerator.bodyBound) * d.numerator.pairBound ^ m)
      d.numerator.pairBound d.numerator.rho n

def retainedOddEnvelope (m n : ℕ) : ℝ :=
  ((d.numerator.prefactorBound * d.numerator.bodyBound) ^ m * d.numerator.pairBound ^ m.choose 2) *
    oddMatchedBound ((d.numerator.prefactorBound * d.numerator.bodyBound) * d.numerator.pairBound ^ m)
      d.numerator.pairBound d.numerator.rho n

theorem fullDensity_collision_jet_bound {m N : ℕ} (x : Fin (m + N) → ℝ)
    {eps E : ℝ} (hN : 0 < m + N) (he : 0 < eps) (he0 : eps ≤ d.eps0)
    (hx : ∀ i : Fin m, |x (Fin.castAdd N i)| ≤ Real.pi)
    (hx0 : (fun i : Fin m => x (Fin.castAdd N i)) ≠ 0)
    (hE : ∀ u ∈ Metric.closedBall (0 : ℂ) d.numerator.radius,
      ‖edgeRetainedNumerator m (affineEdgeCenter b) a u x‖ ≤ E) (j : ℕ) :
    ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x) ((eps : ℂ) * Complex.I)‖ ≤
      d.densityJetConstant j * (m + N : ℕ) ^ j * E *
        retainedCollisionMajorant d.kappa (j + 1) (fun i : Fin m => x (Fin.castAdd N i)) := by
  let q : Fin m → ℝ := fun i => x (Fin.castAdd N i)
  let eta : ℝ := min 1 (d.kappa * angularQuadratic q)
  have hQ : 0 < angularQuadratic q := angularQuadratic_pos_of_ne_zero hx0
  have heta : 0 < eta := lt_min (by norm_num) (mul_pos d.kappa_pos hQ)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hG : eta ≤ (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re :=
    (min_le_right _ _).trans (d.totalPhase_retained_attenuation he he0 x hx)
  have hjet := d.fullDensity_retained_jet_bound x hN heta heta1
    (d.inward_mem eps he he0) hG hE j
  convert hjet using 1
  dsimp [densityJetConstant, retainedCollisionMajorant, RegularEdgePhaseControl.siteRadius, eta, q]
  push_cast
  rw [mul_pow, div_pow, pow_succ]
  field_simp

theorem retainedEvenEnvelope_nonneg (m n : ℕ) : 0 ≤ d.retainedEvenEnvelope m n := by
  have hA := d.numerator.prefactorBound_pos.le
  have hB := d.numerator.bodyBound_pos.le
  have hC := d.numerator.pairBound_pos.le
  have hq := d.numerator.rho_pos.le
  unfold retainedEvenEnvelope evenMatchedBound
  positivity

theorem retainedOddEnvelope_nonneg (m n : ℕ) : 0 ≤ d.retainedOddEnvelope m n := by
  have hA := d.numerator.prefactorBound_pos.le
  have hB := d.numerator.bodyBound_pos.le
  have hC := d.numerator.pairBound_pos.le
  have hq := d.numerator.rho_pos.le
  unfold retainedOddEnvelope oddMatchedBound
  positivity

/-- Every even complementary particle count, with the complete rational
factor, is controlled by a single fixed-block integrable angular factor. -/
theorem fullDensity_even_jet_majorant {m : ℕ} (hm : 0 < m) (j k : ℕ) :
    ∃ H : ℕ → ℝ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) ∧
      (∀ n, 0 ≤ H n) ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
        ∀ n (x : Fin (m + 2 * n) → ℝ),
          (∀ i : Fin m, |x (Fin.castAdd (2 * n) i)| ≤ Real.pi) →
          (fun i : Fin m => x (Fin.castAdd (2 * n) i)) ≠ 0 →
          ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x) ((eps : ℂ) * Complex.I)‖ ≤
            H n * retainedCollisionMajorant d.kappa (j + 1)
              (fun i : Fin m => x (Fin.castAdd (2 * n) i)) := by
  let H : ℕ → ℝ := fun n => d.densityJetConstant j * (m + 2 * n : ℕ) ^ j * d.retainedEvenEnvelope m n
  let A := d.numerator.prefactorBound * d.numerator.bodyBound
  let C := d.numerator.pairBound
  let f := evenMatchedBound (A * C ^ m) C d.numerator.rho
  have hA : 0 ≤ A := mul_nonneg d.numerator.prefactorBound_pos.le d.numerator.bodyBound_pos.le
  have hC : 0 ≤ C := d.numerator.pairBound_pos.le
  have hq : 0 ≤ d.numerator.rho := d.numerator.rho_pos.le
  have hf : ∀ n : ℕ, 0 ≤ f n := by intro n; dsimp [f, evenMatchedBound]; positivity
  have hs := summable_weighted_affine hf (Nat.cast_nonneg m) (by norm_num : (0 : ℝ) ≤ 2) j k
    (summable_evenMatchedBound_polynomial (mul_nonneg hA (pow_nonneg hC m)) hC hq d.numerator.rho_lt_one (k + j))
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) := by
    convert hs.mul_left (d.densityJetConstant j * (A ^ m * C ^ m.choose 2)) using 1
    funext n
    dsimp [H, retainedEvenEnvelope, f, A, C]
    push_cast
    ring
  refine ⟨H, hsum, ?_, ?_⟩
  · intro n
    exact mul_nonneg (mul_nonneg (d.densityJetConstant_pos j).le (by positivity))
      (d.retainedEvenEnvelope_nonneg m n)
  · intro eps he he0 n x hx hx0
    exact d.fullDensity_collision_jet_bound x (by omega) he he0 hx hx0
      (fun u hu => d.numerator.retainedNumerator_even_bound hu n x) j

/-- Every odd complementary particle count is included with the same
fixed-dimensional angular majorant; no intermediate-index range is omitted. -/
theorem fullDensity_odd_jet_majorant {m : ℕ} (hm : 0 < m) (j k : ℕ) :
    ∃ H : ℕ → ℝ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) ∧
      (∀ n, 0 ≤ H n) ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
        ∀ n (x : Fin (m + (2 * n + 1)) → ℝ),
          (∀ i : Fin m, |x (Fin.castAdd (2 * n + 1) i)| ≤ Real.pi) →
          (fun i : Fin m => x (Fin.castAdd (2 * n + 1) i)) ≠ 0 →
          ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x) ((eps : ℂ) * Complex.I)‖ ≤
            H n * retainedCollisionMajorant d.kappa (j + 1)
              (fun i : Fin m => x (Fin.castAdd (2 * n + 1) i)) := by
  let H : ℕ → ℝ := fun n => d.densityJetConstant j * (m + (2 * n + 1) : ℕ) ^ j * d.retainedOddEnvelope m n
  let A := d.numerator.prefactorBound * d.numerator.bodyBound
  let C := d.numerator.pairBound
  let f := oddMatchedBound (A * C ^ m) C d.numerator.rho
  have hA : 0 ≤ A := mul_nonneg d.numerator.prefactorBound_pos.le d.numerator.bodyBound_pos.le
  have hC : 0 ≤ C := d.numerator.pairBound_pos.le
  have hq : 0 ≤ d.numerator.rho := d.numerator.rho_pos.le
  have hf : ∀ n : ℕ, 0 ≤ f n := by intro n; dsimp [f, oddMatchedBound]; positivity
  have hs := summable_weighted_affine hf (by positivity : 0 ≤ (m : ℝ) + 1) (by norm_num : (0 : ℝ) ≤ 2) j k
    (summable_oddMatchedBound_polynomial (mul_nonneg hA (pow_nonneg hC m)) hC hq d.numerator.rho_lt_one (k + j))
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) := by
    convert hs.mul_left (d.densityJetConstant j * (A ^ m * C ^ m.choose 2)) using 1
    funext n
    dsimp [H, retainedOddEnvelope, f, A, C]
    push_cast
    ring
  refine ⟨H, hsum, ?_, ?_⟩
  · intro n
    exact mul_nonneg (mul_nonneg (d.densityJetConstant_pos j).le (by positivity))
      (d.retainedOddEnvelope_nonneg m n)
  · intro eps he he0 n x hx hx0
    exact d.fullDensity_collision_jet_bound x (by omega) he he0 hx hx0
      (fun u hu => d.numerator.retainedNumerator_odd_bound hu n x) j

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
