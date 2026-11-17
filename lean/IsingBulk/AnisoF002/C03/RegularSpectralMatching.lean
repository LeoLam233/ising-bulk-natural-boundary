import IsingBulk.AnisoF002.C03.RegularSchur
import IsingBulk.AnisoF002.RegularTail.FiniteNumerator
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Matched bounds for the literal F002 spectral numerator at every real angle

The finite Schur expansion is first applied where angular denominators are
nonzero.  A common real angular shift avoids all reciprocal pairs on a dense
set.  Continuity of the actual canceled spectral kernel then restores every
tuple, including reciprocal pairs and coincident roots.  No physical pair is
discarded and no root factor is divided out.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

theorem pairProductOn_ofFn {α R : Type*} [CommRing R]
    (K : α → α → R) (N : ℕ) (x : Fin N → α) :
    pairProductOn K (List.ofFn x) =
      ∏ i, ∏ j, if i < j then K (x i) (x j) else 1 := by
  induction N with
  | zero => simp [pairProductOn]
  | succ N ih =>
      rw [List.ofFn_succ, pairProductOn, List.map_ofFn, List.prod_ofFn, ih]
      rw [Fin.prod_univ_succ]
      simp [Fin.prod_univ_succ, Fin.succ_pos]

theorem pairProductOn_indexPairs {α R : Type*} [CommRing R]
    (K : α → α → R) {N : ℕ} (x : Fin N → α) :
    pairProductOn K (List.ofFn x) =
      ∏ ij ∈ indexPairs N, K (x ij.1) (x ij.2) := by
  rw [pairProductOn_ofFn]
  rw [indexPairs, Finset.prod_filter, Finset.prod_product]

theorem countable_bad_angle_shift (a b : ℝ) :
    Set.Countable {t : ℝ | 1 - Complex.exp (((a + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((b + t : ℝ) : ℂ) * Complex.I) = 0} := by
  let f : ℝ → ℂ := fun t => ((a + b + 2 * t : ℝ) : ℂ) * Complex.I
  have hf : Function.Injective f := by
    intro s t h
    have hi := congrArg Complex.im h
    simp only [f, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] at hi
    linarith
  have hc := (Set.countable_singleton (1 : ℂ)).preimage_cexp.preimage hf
  have he (t : ℝ) : Complex.exp (((a + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((b + t : ℝ) : ℂ) * Complex.I) = Complex.exp (f t) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [f]
    push_cast
    ring
  convert hc using 1
  ext t
  change (1 - Complex.exp (((a + t : ℝ) : ℂ) * Complex.I) *
    Complex.exp (((b + t : ℝ) : ℂ) * Complex.I) = 0) ↔ Complex.exp (f t) = 1
  rw [he, sub_eq_zero]
  exact eq_comm

theorem dense_good_angle_shift {N : ℕ} (x : Fin N → ℝ) :
    Dense {t : ℝ | ∀ i j, 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) ≠ 0} := by
  have hc : Set.Countable (⋃ i : Fin N, ⋃ j : Fin N,
      {t : ℝ | 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) = 0}) :=
    Set.countable_iUnion fun i => Set.countable_iUnion fun j =>
      countable_bad_angle_shift (x i) (x j)
  convert hc.dense_compl ℝ using 1
  ext t
  simp

theorem spectralCanceledPairF002_continuous_shift {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (a b : ℝ) :
    Continuous (fun t : ℝ => spectralCanceledPairF002 lam z (a + t) (b + t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hma : ContinuousAt (fun s : ℝ => (z, a + s)) t :=
    continuousAt_const.prodMk (continuousAt_const.add continuousAt_id)
  have hmb : ContinuousAt (fun s : ℝ => (z, b + s)) t :=
    continuousAt_const.prodMk (continuousAt_const.add continuousAt_id)
  have hr : ContinuousAt (fun s : ℝ => spectralSmallRootF002 lam z (a + s)) t :=
    ContinuousAt.comp (g := fun p : ℂ × ℝ => spectralSmallRootF002 lam p.1 p.2)
      (f := fun s : ℝ => (z, a + s)) (x := t)
      (spectralSmallRootF002_continuousAt (a + t) hz) hma
  have hs : ContinuousAt (fun s : ℝ => spectralSmallRootF002 lam z (b + s)) t :=
    ContinuousAt.comp (g := fun p : ℂ × ℝ => spectralSmallRootF002 lam p.1 p.2)
      (f := fun s : ℝ => (z, b + s)) (x := t)
      (spectralSmallRootF002_continuousAt (b + t) hz) hmb
  have hy : ContinuousAt (fun t : ℝ =>
      Complex.exp (((a + t : ℝ) : ℂ) * Complex.I)) t := by fun_prop
  have hv : ContinuousAt (fun t : ℝ =>
      Complex.exp (((b + t : ℝ) : ℂ) * Complex.I)) t := by fun_prop
  unfold spectralCanceledPairF002 canceledPair
  apply (((continuousAt_const.mul ((hy.sub hv).pow 2)).mul hr).mul hs).div
    ((hy.mul hv).mul ((continuousAt_const.sub (hr.mul hs)).pow 2))
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (pow_ne_zero _ (pair_root_denominator_ne_zero
      (spectralSmallRootF002_spec (a + t) hz).2
      (spectralSmallRootF002_spec (b + t) hz).2))

theorem spectral_pairs_even_norm_le_good {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n) → ℝ)
    (hd : ∀ i j, 1 - Complex.exp ((x i : ℂ) * Complex.I) *
      Complex.exp ((x j : ℂ) * Complex.I) ≠ 0) :
    ‖∏ ij ∈ indexPairs (2 * n), spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  have he : (fun i j => schur (spectralSmallRootF002 lam z (x i))
      (spectralSmallRootF002 lam z (x j)) *
      schur (Complex.exp ((x i : ℂ) * Complex.I)) (Complex.exp ((x j : ℂ) * Complex.I))) =
      fun i j => spectralCanceledPairF002 lam z (x i) (x j) := by
    funext i j
    exact spectral_schur_pair_eq_canceled (x i) (x j) hz hS (hd i j)
  have hb := schur_pair_product_even_bound
    (fun i => spectralSmallRootF002 lam z (x i))
    (fun i => Complex.exp ((x i : ℂ) * Complex.I)) hq hC
    (fun i j => hroot (x i) (x j))
    (fun i j => by
      rw [spectral_schur_pair_eq_canceled (x i) (x j) hz hS (hd i j)]
      exact hpair (x i) (x j)) hd n (List.ofFn (id : Fin (2 * n) → _))
    (by simp)
  rw [he, pairProductOn_indexPairs] at hb
  exact hb

theorem spectral_pairs_odd_norm_le_good {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n + 1) → ℝ)
    (hd : ∀ i j, 1 - Complex.exp ((x i : ℂ) * Complex.I) *
      Complex.exp ((x j : ℂ) * Complex.I) ≠ 0) :
    ‖∏ ij ∈ indexPairs (2 * n + 1), spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
  have he : (fun i j => schur (spectralSmallRootF002 lam z (x i))
      (spectralSmallRootF002 lam z (x j)) *
      schur (Complex.exp ((x i : ℂ) * Complex.I)) (Complex.exp ((x j : ℂ) * Complex.I))) =
      fun i j => spectralCanceledPairF002 lam z (x i) (x j) := by
    funext i j
    exact spectral_schur_pair_eq_canceled (x i) (x j) hz hS (hd i j)
  have hg : ∀ i, Complex.exp ((x i : ℂ) * Complex.I) ≠ -1 := by
    intro i hi
    apply hd i i
    simp [hi]
  have hb := schur_pair_product_odd_bound
    (fun i => spectralSmallRootF002 lam z (x i))
    (fun i => Complex.exp ((x i : ℂ) * Complex.I)) hq hC
    (fun i j => hroot (x i) (x j))
    (fun i j => by
      rw [spectral_schur_pair_eq_canceled (x i) (x j) hz hS (hd i j)]
      exact hpair (x i) (x j)) hd hg n
    (List.ofFn (id : Fin (2 * n + 1) → _)) (by simp)
  rw [he, pairProductOn_indexPairs] at hb
  exact hb

/-- Exact even matched bound for the literal canceled spectral product, with
every real angular tuple restored. The root contraction and complete-pair
bound are distinct hypotheses, as required by frozen F002. -/
theorem spectral_pairs_even_norm_le {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n), spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  have hc : Continuous (fun t : ℝ =>
      ∏ ij ∈ indexPairs (2 * n), spectralCanceledPairF002 lam z (x ij.1 + t) (x ij.2 + t)) := by
    apply continuous_finsetProd
    intro ij _
    exact spectralCanceledPairF002_continuous_shift hz _ _
  have hclosed := isClosed_le hc.norm
    (continuous_const : Continuous (fun _ : ℝ =>
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))))
  have hsub : {t : ℝ | ∀ i j, 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) ≠ 0} ⊆
      {t : ℝ | ‖∏ ij ∈ indexPairs (2 * n),
        spectralCanceledPairF002 lam z (x ij.1 + t) (x ij.2 + t)‖ ≤
          (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))} := by
    intro t ht
    exact spectral_pairs_even_norm_le_good hz hS hq hC hroot hpair n (fun i => x i + t) ht
  simpa using closure_minimal hsub hclosed ((dense_good_angle_shift x) 0)

/-- Exact odd bound, including the removable ghost and every reciprocal or
coincident angular tuple. The unmatched exponent is `(N-1)^2/2`. -/
theorem spectral_pairs_odd_norm_le {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hroot : ∀ a b : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z b)‖ ≤ q)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n + 1), spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
  have hc : Continuous (fun t : ℝ =>
      ∏ ij ∈ indexPairs (2 * n + 1), spectralCanceledPairF002 lam z (x ij.1 + t) (x ij.2 + t)) := by
    apply continuous_finsetProd
    intro ij _
    exact spectralCanceledPairF002_continuous_shift hz _ _
  have hclosed := isClosed_le hc.norm
    (continuous_const : Continuous (fun _ : ℝ =>
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)))
  have hsub : {t : ℝ | ∀ i j, 1 - Complex.exp (((x i + t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x j + t : ℝ) : ℂ) * Complex.I) ≠ 0} ⊆
      {t : ℝ | ‖∏ ij ∈ indexPairs (2 * n + 1),
        spectralCanceledPairF002 lam z (x ij.1 + t) (x ij.2 + t)‖ ≤
          (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)} := by
    intro t ht
    exact spectral_pairs_odd_norm_le_good hz hS hq hC hroot hpair n (fun i => x i + t) ht
  simpa using closure_minimal hsub hclosed ((dense_good_angle_shift x) 0)

end
end IsingBulk.AnisoF002.RegularTail.C03
