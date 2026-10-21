import IsingBulk.HT.Tail.UpperOddSeries
import IsingBulk.Tail.AllOrderTailDomination
import IsingBulk.Final.AbsoluteTail
import IsingBulk.Final.UpperNoncancellation

/-!
# The literal infinite odd tail

The indexing begins at `p+2` and covers exactly every odd order greater
than an odd first order `p`.  The normal-convergence theorem proves actual
summability before any `tsum` comparison is made.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Filter Set Asymptotics
open scoped Topology BigOperators

def oddTailParticle (p n : ℕ) : ℕ := p + 2 * (n + 1)

theorem oddTailParticle_injective (p : ℕ) : Function.Injective (oddTailParticle p) := by
  intro a b h
  dsimp [oddTailParticle] at h
  omega

theorem oddTailParticle_gt (p n : ℕ) : p < oddTailParticle p n := by
  dsimp [oddTailParticle]
  omega

theorem oddTailParticle_eq_index {p : ℕ} (hp : Odd p) (n : ℕ) :
    oddTailParticle p n = 2 * (n + (p + 1) / 2) + 1 := by
  rcases hp with ⟨q, hq⟩
  dsimp [oddTailParticle]
  omega

/-- The enumeration is exact and contains arbitrarily large particle
numbers.  There is no omitted upper particle-number window. -/
theorem mem_oddTailParticle_range {p N : ℕ} (hp : Odd p) :
    (∃ n, oddTailParticle p n = N) ↔ p < N ∧ Odd N := by
  rcases hp with ⟨q, hq⟩
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨oddTailParticle_gt p n, ⟨q + n + 1, ?_⟩⟩
    dsimp [oddTailParticle]
    omega
  · rintro ⟨hNp, m, hm⟩
    refine ⟨m - q - 1, ?_⟩
    dsimp [oddTailParticle]
    omega

theorem actual_upper_odd_tail_summable {p : ℕ} (hp : Odd p) (j : ℕ)
    {theta eps : ℝ} (htheta : 0 < Real.sin theta) (heps : 0 < eps) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter theta eps)‖) := by
  have hs := (upperOdd_derivative_summable j
    (IsingBulk.Final.sourceRadialTrace_pos htheta heps)).comp_injective
      (show Function.Injective (fun n : ℕ => n + (p + 1) / 2) from
        fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, oddTailParticle_eq_index hp] using hs

/-- Exact low/first/infinite-high partition of the differentiated series.
The supplied equality merely writes the chosen odd first order as `2*q+1`.
Its analytic content comes from the internally proved normal convergence. -/
theorem upperOddSeries_radial_split (q j : ℕ) {theta eps : ℝ}
    (htheta : 0 < Real.sin theta) (heps : 0 < eps) :
    iteratedDeriv j upperOddSeries (radialParameter theta eps) =
      (∑ n ∈ Finset.range q,
        iteratedDeriv j (upperFormFactor (2 * n + 1)) (radialParameter theta eps)) +
      iteratedDeriv j (upperFormFactor (2 * q + 1)) (radialParameter theta eps) +
      ∑' n : ℕ, iteratedDeriv j (upperFormFactor (oddTailParticle (2 * q + 1) n))
        (radialParameter theta eps) := by
  have hs := IsingBulk.Final.sourceRadialTrace_pos htheta heps
  rw [upperOddSeries_iteratedDeriv j hs]
  have hsum := (upperOdd_derivative_summable j hs).of_norm.sum_add_tsum_nat_add (q + 1)
  rw [Finset.sum_range_succ] at hsum
  have hindex (n : ℕ) : 2 * (n + (q + 1)) + 1 = oddTailParticle (2 * q + 1) n := by
    dsimp [oddTailParticle]
    omega
  simpa only [hindex] using hsum.symm

/-- A nonnegative sequence can be restricted to the exact odd tail and
split at any real threshold.  The infinite high sum is never truncated. -/
theorem nonnegative_odd_tail_window_split (v : ℕ → ℝ) (hv : ∀ N, 0 ≤ v N)
    (hs : Summable v) (p : ℕ) (T : ℝ) :
    (∑' n : ℕ, v (oddTailParticle p n)) ≤
      (∑' N : ℕ, if p + 2 ≤ N ∧ (N : ℝ) < T then v N else 0) +
      (∑' N : ℕ, if T ≤ (N : ℝ) then v N else 0) := by
  let low := fun N : ℕ => if p + 2 ≤ N then v N else 0
  let mid := fun N : ℕ => if p + 2 ≤ N ∧ (N : ℝ) < T then v N else 0
  let high := fun N : ℕ => if T ≤ (N : ℝ) then v N else 0
  have hlow : Summable low := hs.of_nonneg_of_le
    (fun N => by dsimp [low]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [low]; split_ifs <;> simp [hv N])
  have hmid : Summable mid := hs.of_nonneg_of_le
    (fun N => by dsimp [mid]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [mid]; split_ifs <;> simp [hv N])
  have hhigh : Summable high := hs.of_nonneg_of_le
    (fun N => by dsimp [high]; split_ifs <;> simp [hv N])
    (fun N => by dsimp [high]; split_ifs <;> simp [hv N])
  have hfirst : (∑' n : ℕ, v (oddTailParticle p n)) ≤ ∑' N, low N :=
    (hs.comp_injective (oddTailParticle_injective p)).tsum_le_tsum_of_inj _
      (oddTailParticle_injective p)
      (fun N _ => by dsimp [low]; split_ifs <;> simp [hv N])
      (fun n => by dsimp [low]; rw [ite_eq_left (by dsimp [oddTailParticle]; omega)]) hlow
  have hpoint (N : ℕ) : low N ≤ mid N + high N := by
    by_cases hL : p + 2 ≤ N
    · by_cases hT : (N : ℝ) < T
      · simp [low, mid, high, hL, hT, not_le.mpr hT]
      · simp [low, mid, high, hL, hT, le_of_not_gt hT]
    · dsimp [low, mid, high]
      simp only [hL, false_and, ite_false, zero_add]
      split_ifs <;> simp [hv N]
  exact hfirst.trans ((Summable.tsum_le_tsum hpoint hlow (hmid.add hhigh)).trans_eq
    (hmid.tsum_add hhigh))

/-- This is an explicit target proposition, not an asserted tail theorem.
Its proof still requires the HT selected, intermediate and signed sectors. -/
def AbsoluteUpperOddTailSmall (p : ℕ) (theta : ℝ) (j : ℕ) : Prop :=
  IsLittleO (𝓝[>] (0 : ℝ))
    (fun eps => ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter theta eps)‖)
    (fun eps => (Real.sqrt eps)⁻¹)

/-- A conditional algebraic bridge for final assembly: the hypothesis is
the literal absolute infinite tail, and convergence is proved separately.
This lemma is not an unconditional HT tail endpoint. -/
theorem complex_odd_tail_small_of_absolute {p : ℕ} (hp : Odd p)
    {theta : ℝ} (htheta : 0 < Real.sin theta) (j : ℕ)
    (hTail : AbsoluteUpperOddTailSmall p theta j) :
    IsLittleO (𝓝[>] (0 : ℝ))
      (fun eps => ∑' n : ℕ, iteratedDeriv j (upperFormFactor (oddTailParticle p n))
        (radialParameter theta eps)) (fun eps => (Real.sqrt eps : ℂ)⁻¹) := by
  apply IsingBulk.Final.complex_tail_isLittleO_of_absolute _ hTail
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact actual_upper_odd_tail_summable hp j htheta heps

end
end IsingBulk.HT.Tail
