import IsingBulk.AnisoF002.C03.RegularSpectralMatching

/-!
# Matched bounds on a continued branch of the actual unsquared dispersion

The branch is allowed to pass across the spectral frontier.  Its defining
quadratic is required explicitly, and the complete canceled pair is the
same literal F002 function.  On the physical interior the canonical-root
specialization is definitional.  These intermediate branch bounds supply
no additional premise to the terminal physical theorem.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

def branchCanceledPair (B : ℂ) (r : ℝ → ℂ) (a b : ℝ) : ℂ :=
  canceledPair B (r a) (r b) (Complex.exp ((a : ℂ) * Complex.I))
    (Complex.exp ((b : ℂ) * Complex.I))

def branchOneBody (r : ℝ → ℂ) (a : ℝ) : ℂ := 2 * r a / (1 - (r a) ^ 2)

def branchFullNumerator {N : ℕ} (B b : ℂ) (r : ℝ → ℂ) (x : Fin N → ℝ) : ℂ :=
  b ^ N * (∏ i, branchOneBody r (x i)) *
    ∏ ij ∈ indexPairs N, branchCanceledPair B r (x ij.1) (x ij.2)

theorem branchFullNumerator_canonical (lam : ℝ) (z b : ℂ) {N : ℕ} (x : Fin N → ℝ) :
    branchFullNumerator (IsingBulk.Anisotropic.spectralT lam z / IsingBulk.Anisotropic.spectralS z)
      b (IsingBulk.AnisoF002.Geometry.spectralSmallRootF002 lam z) x =
      fullRootNumeratorF002 lam z b x := rfl

theorem dispersion_exp_angle {S T A : ℂ} {r : ℝ → ℂ} (a : ℝ)
    (hp : S * (r a) ^ 2 - 2 * (A - T * (Real.cos a : ℂ)) * r a + S = 0) :
    S * Complex.exp ((a : ℂ) * Complex.I) * ((r a) ^ 2 + 1) -
      2 * A * Complex.exp ((a : ℂ) * Complex.I) * r a +
      T * ((Complex.exp ((a : ℂ) * Complex.I)) ^ 2 + 1) * r a = 0 := by
  have hc : 2 * (Real.cos a : ℂ) * Complex.exp ((a : ℂ) * Complex.I) =
      (Complex.exp ((a : ℂ) * Complex.I)) ^ 2 + 1 := by
    rw [Complex.ofReal_cos, Complex.two_cos, add_mul]
    have he : Complex.exp (-(a : ℂ) * Complex.I) *
        Complex.exp ((a : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
    rw [he, ← pow_two]
  linear_combination Complex.exp ((a : ℂ) * Complex.I) * hp - T * r a * hc

theorem dispersion_schur_pair_eq {S T A : ℂ} {r : ℝ → ℂ}
    (hS : S ≠ 0)
    (hdisp : ∀ a : ℝ, S * (r a) ^ 2 - 2 * (A - T * (Real.cos a : ℂ)) * r a + S = 0)
    (hden : ∀ a b : ℝ, 1 - r a * r b ≠ 0)
    (a b : ℝ) (hangle : 1 - Complex.exp ((a : ℂ) * Complex.I) *
      Complex.exp ((b : ℂ) * Complex.I) ≠ 0) :
    schur (r a) (r b) *
      schur (Complex.exp ((a : ℂ) * Complex.I)) (Complex.exp ((b : ℂ) * Complex.I)) =
      branchCanceledPair (T / S) r a b := by
  exact schur_pair_eq_canceled hS (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (hden a b) hangle (dispersion_exp_angle a (hdisp a)) (dispersion_exp_angle b (hdisp b))

theorem branchCanceledPair_continuous_shift (B : ℂ) (r : ℝ → ℂ)
    (hr : Continuous r) (hden : ∀ a b : ℝ, 1 - r a * r b ≠ 0) (a b : ℝ) :
    Continuous (fun t : ℝ => branchCanceledPair B r (a + t) (b + t)) := by
  have hrr : Continuous (fun t : ℝ => r (a + t)) := hr.comp (continuous_const.add continuous_id)
  have hrs : Continuous (fun t : ℝ => r (b + t)) := hr.comp (continuous_const.add continuous_id)
  have hy : Continuous (fun t : ℝ => Complex.exp (((a + t : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hv : Continuous (fun t : ℝ => Complex.exp (((b + t : ℝ) : ℂ) * Complex.I)) := by fun_prop
  unfold branchCanceledPair canceledPair
  apply (((continuous_const.mul ((hy.sub hv).pow 2)).mul hrr).mul hrs).div
    ((hy.mul hv).mul ((continuous_const.sub (hrr.mul hrs)).pow 2))
  intro t
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (pow_ne_zero _ (hden (a + t) (b + t)))

theorem branch_pairs_even_norm_le {S T A : ℂ} {r : ℝ → ℂ}
    (hS : S ≠ 0) (hr : Continuous r)
    (hdisp : ∀ a : ℝ, S * (r a) ^ 2 - 2 * (A - T * (Real.cos a : ℂ)) * r a + S = 0)
    (hden : ∀ a b : ℝ, 1 - r a * r b ≠ 0)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hroot : ∀ a b : ℝ, ‖schur (r a) (r b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖branchCanceledPair (T / S) r a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n), branchCanceledPair (T / S) r (x ij.1) (x ij.2)‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  have hgood (y : Fin (2 * n) → ℝ)
      (hd : ∀ i j, 1 - Complex.exp ((y i : ℂ) * Complex.I) *
        Complex.exp ((y j : ℂ) * Complex.I) ≠ 0) :
      ‖∏ ij ∈ indexPairs (2 * n), branchCanceledPair (T / S) r (y ij.1) (y ij.2)‖ ≤
        (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
    have he : (fun i j => schur (r (y i)) (r (y j)) *
        schur (Complex.exp ((y i : ℂ) * Complex.I)) (Complex.exp ((y j : ℂ) * Complex.I))) =
        fun i j => branchCanceledPair (T / S) r (y i) (y j) := by
      funext i j
      exact dispersion_schur_pair_eq hS hdisp hden (y i) (y j) (hd i j)
    have hb := schur_pair_product_even_bound (fun i => r (y i))
      (fun i => Complex.exp ((y i : ℂ) * Complex.I)) hq hC
      (fun i j => hroot (y i) (y j))
      (fun i j => by
        rw [dispersion_schur_pair_eq hS hdisp hden (y i) (y j) (hd i j)]
        exact hpair (y i) (y j)) hd n (List.ofFn (id : Fin (2 * n) → _)) (by simp)
    rw [he, pairProductOn_indexPairs] at hb
    exact hb
  have hc : Continuous (fun t : ℝ =>
      ∏ ij ∈ indexPairs (2 * n), branchCanceledPair (T / S) r (x ij.1 + t) (x ij.2 + t)) := by
    apply continuous_finsetProd
    intro ij _
    exact branchCanceledPair_continuous_shift _ _ hr hden _ _
  have hclosed := isClosed_le hc.norm
    (continuous_const : Continuous (fun _ : ℝ =>
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))))
  have hsub : {t : ℝ | ∀ i j, 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) ≠ 0} ⊆
      {t : ℝ | ‖∏ ij ∈ indexPairs (2 * n),
        branchCanceledPair (T / S) r (x ij.1 + t) (x ij.2 + t)‖ ≤
          (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))} := by
    intro t ht
    exact hgood (fun i => x i + t) ht
  simpa using closure_minimal hsub hclosed ((dense_good_angle_shift x) 0)

theorem branch_pairs_odd_norm_le {S T A : ℂ} {r : ℝ → ℂ}
    (hS : S ≠ 0) (hr : Continuous r)
    (hdisp : ∀ a : ℝ, S * (r a) ^ 2 - 2 * (A - T * (Real.cos a : ℂ)) * r a + S = 0)
    (hden : ∀ a b : ℝ, 1 - r a * r b ≠ 0)
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hroot : ∀ a b : ℝ, ‖schur (r a) (r b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖branchCanceledPair (T / S) r a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n + 1), branchCanceledPair (T / S) r (x ij.1) (x ij.2)‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
  have hgood (y : Fin (2 * n + 1) → ℝ)
      (hd : ∀ i j, 1 - Complex.exp ((y i : ℂ) * Complex.I) *
        Complex.exp ((y j : ℂ) * Complex.I) ≠ 0) :
      ‖∏ ij ∈ indexPairs (2 * n + 1), branchCanceledPair (T / S) r (y ij.1) (y ij.2)‖ ≤
        (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
    have he : (fun i j => schur (r (y i)) (r (y j)) *
        schur (Complex.exp ((y i : ℂ) * Complex.I)) (Complex.exp ((y j : ℂ) * Complex.I))) =
        fun i j => branchCanceledPair (T / S) r (y i) (y j) := by
      funext i j
      exact dispersion_schur_pair_eq hS hdisp hden (y i) (y j) (hd i j)
    have hg : ∀ i, Complex.exp ((y i : ℂ) * Complex.I) ≠ -1 := by
      intro i hi
      apply hd i i
      simp [hi]
    have hb := schur_pair_product_odd_bound (fun i => r (y i))
      (fun i => Complex.exp ((y i : ℂ) * Complex.I)) hq hC
      (fun i j => hroot (y i) (y j))
      (fun i j => by
        rw [dispersion_schur_pair_eq hS hdisp hden (y i) (y j) (hd i j)]
        exact hpair (y i) (y j)) hd hg n (List.ofFn (id : Fin (2 * n + 1) → _)) (by simp)
    rw [he, pairProductOn_indexPairs] at hb
    exact hb
  have hc : Continuous (fun t : ℝ =>
      ∏ ij ∈ indexPairs (2 * n + 1), branchCanceledPair (T / S) r (x ij.1 + t) (x ij.2 + t)) := by
    apply continuous_finsetProd
    intro ij _
    exact branchCanceledPair_continuous_shift _ _ hr hden _ _
  have hclosed := isClosed_le hc.norm
    (continuous_const : Continuous (fun _ : ℝ =>
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)))
  have hsub : {t : ℝ | ∀ i j, 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) ≠ 0} ⊆
      {t : ℝ | ‖∏ ij ∈ indexPairs (2 * n + 1),
        branchCanceledPair (T / S) r (x ij.1 + t) (x ij.2 + t)‖ ≤
          (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)} := by
    intro t ht
    exact hgood (fun i => x i + t) ht
  simpa using closure_minimal hsub hclosed ((dense_good_angle_shift x) 0)

end
end IsingBulk.AnisoF002.RegularTail.C03
