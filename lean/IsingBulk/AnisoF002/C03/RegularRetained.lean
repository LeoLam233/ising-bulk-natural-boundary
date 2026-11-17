import IsingBulk.AnisoF002.C03.RegularNumerator

/-!
# Retaining the actual fixed sine block before matching the complete tail

All pairs internal to the first `m` labels use the already constructed
analytic sine quotient.  Every cross pair is kept, at cost `C^(m*N)`.
The full pair product on the remaining labels receives the matched bound.
This is the exact finite factorization needed for the frozen F002
fixed-sub-Vandermonde estimate; no subset of particle indices is removed.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

theorem pairProductOn_append {α R : Type*} [CommRing R]
    (K : α → α → R) (xs ys : List α) :
    pairProductOn K (xs ++ ys) = pairProductOn K xs *
      (xs.map (fun a => (ys.map (K a)).prod)).prod * pairProductOn K ys := by
  induction xs with
  | nil => simp [pairProductOn]
  | cons a xs ih =>
      simp only [List.cons_append, pairProductOn, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons, ih]
      ring

theorem pairProductOn_norm_le {α : Type*} (K : α → α → ℂ) (xs : List α)
    {D : ℝ} (hD : 0 ≤ D) (hK : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ D) :
    ‖pairProductOn K xs‖ ≤ D ^ xs.length.choose 2 := by
  induction xs with
  | nil => simp [pairProductOn]
  | cons a xs ih =>
      rw [pairProductOn, norm_mul]
      have hp := norm_list_prod_le_pow xs (K a) hD
        (fun b hb => hK a (by simp) b (by simp [hb]))
      have ht := ih (fun b hb c hc => hK b (by simp [hb]) c (by simp [hc]))
      calc
        ‖(xs.map (K a)).prod‖ * ‖pairProductOn K xs‖ ≤
            D ^ xs.length * D ^ xs.length.choose 2 :=
          mul_le_mul hp ht (norm_nonneg _) (pow_nonneg hD _)
        _ = D ^ (a :: xs).length.choose 2 := by
          rw [← pow_add]
          congr 1
          simp [Nat.choose_succ_succ]

theorem pairProductOn_split_norm_le {α : Type*} (K : α → α → ℂ) (xs ys : List α)
    {D C E : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hhead : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ D)
    (hcross : ∀ a ∈ xs, ∀ b ∈ ys, ‖K a b‖ ≤ C)
    (htail : ‖pairProductOn K ys‖ ≤ E) :
    ‖pairProductOn K (xs ++ ys)‖ ≤
      D ^ xs.length.choose 2 * C ^ (xs.length * ys.length) * E := by
  have hh := pairProductOn_norm_le K xs hD hhead
  have hc : ‖(xs.map (fun a => (ys.map (K a)).prod)).prod‖ ≤
      C ^ (xs.length * ys.length) := by
    have hp := norm_list_prod_le_pow xs (fun a => (ys.map (K a)).prod)
      (pow_nonneg hC ys.length)
      (fun a ha => norm_list_prod_le_pow ys (K a) hC (hcross a ha))
    simpa only [← pow_mul, Nat.mul_comm] using hp
  rw [pairProductOn_append, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hh hc (norm_nonneg _) (pow_nonneg hD _)) htail
    (norm_nonneg _) (mul_nonneg (pow_nonneg hD _) (pow_nonneg hC _))

theorem retained_pair_product_norm_le {m N : ℕ} (lam : ℝ) (z : ℂ)
    (x : Fin (m + N) → ℝ) {D C E : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hcoeff : ∀ a b : ℝ, ‖spectralSinePairCoefficientF002 lam z a b‖ ≤ D)
    (hpair : ∀ a b : ℝ, ‖spectralCanceledPairF002 lam z a b‖ ≤ C)
    (htail : ‖∏ ij ∈ indexPairs N,
      spectralCanceledPairF002 lam z (x (ij.1.natAdd m)) (x (ij.2.natAdd m))‖ ≤ E) :
    ‖∏ ij ∈ indexPairs (m + N), if ij.1.val < m ∧ ij.2.val < m then
      spectralSinePairCoefficientF002 lam z (x ij.1) (x ij.2)
      else spectralCanceledPairF002 lam z (x ij.1) (x ij.2)‖ ≤
        D ^ m.choose 2 * C ^ (m * N) * E := by
  let K : Fin (m + N) → Fin (m + N) → ℂ := fun i j =>
    if i.val < m ∧ j.val < m then spectralSinePairCoefficientF002 lam z (x i) (x j)
    else spectralCanceledPairF002 lam z (x i) (x j)
  let xs : List (Fin (m + N)) := List.ofFn fun i : Fin m => i.castLE (Nat.le_add_right m N)
  let ys : List (Fin (m + N)) := List.ofFn fun i : Fin N => i.natAdd m
  have hh : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ D := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    simpa [K, i.isLt, j.isLt] using hcoeff (x (i.castLE _)) (x (j.castLE _))
  have hc : ∀ a ∈ xs, ∀ b ∈ ys, ‖K a b‖ ≤ C := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    have hj : ¬ (j.natAdd m).val < m := by simp
    simpa [K, hj] using hpair (x (i.castLE _)) (x (j.natAdd m))
  have ht : ‖pairProductOn K ys‖ ≤ E := by
    dsimp [ys]
    rw [pairProductOn_indexPairs]
    have he : ∀ ij ∈ indexPairs N, K (ij.1.natAdd m) (ij.2.natAdd m) =
        spectralCanceledPairF002 lam z (x (ij.1.natAdd m)) (x (ij.2.natAdd m)) := by
      intro ij _
      simp [K]
    rw [Finset.prod_congr rfl he]
    exact htail
  have hb := pairProductOn_split_norm_le K xs ys hD hC hh hc ht
  have hl : List.ofFn (id : Fin (m + N) → _) = xs ++ ys := List.ofFn_add
  rw [← hl, pairProductOn_indexPairs] at hb
  simpa only [xs, ys, List.length_ofFn, id_eq, K] using hb

/-- The exact analytic quotient constructed in C02 inherits a bound from
the complete complementary product; the power `b^(m+N)` is retained. -/
theorem retainedNumeratorQuotientF002_norm_le {m N : ℕ} (lam : ℝ) (z b : ℂ)
    (x : Fin (m + N) → ℝ) {M D C E : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (hcoeff : ∀ a c : ℝ, ‖spectralSinePairCoefficientF002 lam z a c‖ ≤ D)
    (hpair : ∀ a c : ℝ, ‖spectralCanceledPairF002 lam z a c‖ ≤ C)
    (htail : ‖∏ ij ∈ indexPairs N,
      spectralCanceledPairF002 lam z (x (ij.1.natAdd m)) (x (ij.2.natAdd m))‖ ≤ E) :
    ‖retainedNumeratorQuotientF002 m lam z b x‖ ≤
      (‖b‖ * M) ^ (m + N) * (D ^ m.choose 2 * C ^ (m * N) * E) := by
  have hprod : ‖∏ i, spectralOneBodyF002 lam z (x i)‖ ≤ M ^ (m + N) := by
    simpa only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def, id_eq] using
      norm_list_prod_le_pow (List.ofFn (id : Fin (m + N) → _))
        (fun i => spectralOneBodyF002 lam z (x i)) hM (fun i _ => hbody (x i))
  have hp := retained_pair_product_norm_le lam z x hD hC hcoeff hpair htail
  unfold retainedNumeratorQuotientF002
  rw [norm_mul, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hprod (pow_nonneg (norm_nonneg b) _)) hp
    (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg b) _) (pow_nonneg hM _))

theorem retainedNumeratorQuotientF002_even_norm_le {m : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C M D : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hroot : ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z c)‖ ≤ q)
    (hpair : ∀ a c : ℝ, ‖spectralCanceledPairF002 lam z a c‖ ≤ C)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (hcoeff : ∀ a c : ℝ, ‖spectralSinePairCoefficientF002 lam z a c‖ ≤ D)
    (n : ℕ) (b : ℂ) (x : Fin (m + 2 * n) → ℝ) :
    ‖retainedNumeratorQuotientF002 m lam z b x‖ ≤
      (‖b‖ * M) ^ (m + 2 * n) * (D ^ m.choose 2 * C ^ (m * (2 * n)) *
        ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)))) := by
  exact retainedNumeratorQuotientF002_norm_le lam z b x hM hD hC hbody hcoeff hpair
    (spectral_pairs_even_norm_le hz hS hq hC hroot hpair n (fun i => x (i.natAdd m)))

theorem retainedNumeratorQuotientF002_odd_norm_le {m : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    {q C M D : ℝ} (hq : 0 < q) (hC : 0 < C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hroot : ∀ a c : ℝ,
      ‖schur (spectralSmallRootF002 lam z a) (spectralSmallRootF002 lam z c)‖ ≤ q)
    (hpair : ∀ a c : ℝ, ‖spectralCanceledPairF002 lam z a c‖ ≤ C)
    (hbody : ∀ a : ℝ, ‖spectralOneBodyF002 lam z a‖ ≤ M)
    (hcoeff : ∀ a c : ℝ, ‖spectralSinePairCoefficientF002 lam z a c‖ ≤ D)
    (n : ℕ) (b : ℂ) (x : Fin (m + (2 * n + 1)) → ℝ) :
    ‖retainedNumeratorQuotientF002 m lam z b x‖ ≤
      (‖b‖ * M) ^ (m + (2 * n + 1)) * (D ^ m.choose 2 * C ^ (m * (2 * n + 1)) *
        ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n))) := by
  exact retainedNumeratorQuotientF002_norm_le lam z b x hM hD hC.le hbody hcoeff hpair
    (spectral_pairs_odd_norm_le hz hS hq hC hroot hpair n (fun i => x (i.natAdd m)))

end
end IsingBulk.AnisoF002.RegularTail.C03
