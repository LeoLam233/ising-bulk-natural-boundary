import IsingBulk.AnisoF002.C03.PhysicalContourAnalytic
import IsingBulk.Anisotropic.Algebra.SchurHadamard

/-!
# All-particle Schur bounds on the actual physical contour

The only historical theorem used here is the separately audited generic
even-dimensional double Schur/Hadamard inequality.  The original indexed
pair product is matched explicitly, and odd particle numbers retain the
full r^(2N) loss from the auxiliary zero coordinates.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.First
open scoped BigOperators

theorem literal_pairProduct_eq_list (N : ℕ) (x : Fin N → ℂ) :
    First.pairProduct x = IsingBulk.Schur.pairProduct First.pairKernel (List.ofFn x) := by
  induction N with
  | zero => simp only [First.pairProduct, Finset.univ_eq_empty, Finset.prod_empty,
      List.ofFn_zero, IsingBulk.Schur.pairProduct]
  | succ N ih =>
    rw [List.ofFn_succ, IsingBulk.Schur.pairProduct, List.map_ofFn, List.prod_ofFn]
    rw [← ih (fun i => x i.succ)]
    simp only [First.pairProduct, Finset.prod_filter]
    rw [Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ, Fin.succ_pos, ite_true, not_lt_zero, ite_false,
      Fin.succ_lt_succ_iff, one_mul, Function.comp_apply]

def literalContourKernelBound (r : ℝ) : ℝ := 2 / (1 - r ^ 2)

theorem literalContourKernelBound_ge_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ literalContourKernelBound r := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg r]

theorem literal_disk_pairKernel_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {x y : ℂ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖First.pairKernel x y‖ ≤ literalContourKernelBound r := by
  have hp : ‖x * y‖ ≤ r ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hx hy (norm_nonneg _) hr
  have hd : 1 - r ^ 2 ≤ ‖1 - x * y‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (x * y)
    rw [norm_one] at hh
    linarith
  have hn : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  unfold First.pairKernel literalContourKernelBound
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hn (by nlinarith) hd

theorem literal_even_disk_pairProduct_bound (N : ℕ) (hN : 0 < N) (heven : Even N)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ r) (hy : ∀ i, ‖y i‖ ≤ r) :
    ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤
      literalContourKernelBound r ^ N * (N : ℝ) ^ (N / 2) := by
  obtain ⟨n, hn⟩ := heven
  have he : N = 2 * n := by omega
  clear hn
  subst N
  rw [literal_pairProduct_eq_list, literal_pairProduct_eq_list]
  have hh := Algebra.even_double_pairProduct_bound (by omega : 0 < n) x y
    (fun i j => pair_root_denominator_ne_zero ((hx i).trans_lt hr1) ((hx j).trans_lt hr1))
    (fun i j => pair_root_denominator_ne_zero ((hy i).trans_lt hr1) ((hy j).trans_lt hr1))
    (show 0 ≤ literalContourKernelBound r from
      zero_le_one.trans (literalContourKernelBound_ge_one hr hr1))
    (fun i j => literal_disk_pairKernel_bound hr hr1 (hx i) (hx j))
    (fun i j => literal_disk_pairKernel_bound hr hr1 (hy i) (hy j))
  convert hh using 1 <;> norm_num
  rfl

theorem literal_pairProduct_cons_zero_norm (N : ℕ) {r : ℝ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = r) :
    ‖First.pairProduct (Fin.cons 0 x)‖ = r ^ N * ‖First.pairProduct x‖ := by
  rw [literal_pairProduct_eq_list, literal_pairProduct_eq_list, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, IsingBulk.Schur.pairProduct,
    List.map_ofFn, List.prod_ofFn, Function.comp_apply, First.pairKernel, zero_sub,
    zero_mul, sub_zero, div_one, norm_mul, norm_prod, norm_neg, hx,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem literal_odd_circle_pairProduct_bound (N : ℕ) (hodd : Odd N)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = r) (hy : ∀ i, ‖y i‖ = r) :
    r ^ (2 * N) * (‖First.pairProduct x‖ * ‖First.pairProduct y‖) ≤
      literalContourKernelBound r ^ (N + 1) * (N + 1 : ℝ) ^ ((N + 1) / 2) := by
  have heven : Even (N + 1) := hodd.add_odd (by decide : Odd 1)
  have hh := literal_even_disk_pairProduct_bound (N + 1) (by omega) heven hr hr1
    (Fin.cons 0 x) (Fin.cons 0 y)
    (fun i => Fin.cases (by simpa using hr) (fun j => (hx j).le) i)
    (fun i => Fin.cases (by simpa using hr) (fun j => (hy j).le) i)
  rw [literal_pairProduct_cons_zero_norm N x hx, literal_pairProduct_cons_zero_norm N y hy] at hh
  convert hh using 1 <;> push_cast <;> ring

def literalContourPairBound (r : ℝ) : ℝ := 2 * literalContourKernelBound r / r ^ 2

theorem literal_circle_pairProduct_bound (N : ℕ) (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = r) (hy : ∀ i, ‖y i‖ = r) :
    ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤
      literalContourKernelBound r * literalContourPairBound r ^ N * (N : ℝ) ^ (N - N / 2) := by
  have hC := literalContourKernelBound_ge_one hr.le hr1
  have hC0 : 0 ≤ literalContourKernelBound r := zero_le_one.trans hC
  have hCK : literalContourKernelBound r ≤ literalContourPairBound r := by
    unfold literalContourPairBound
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    have hsq : r ^ 2 ≤ 1 := by nlinarith
    nlinarith
  rcases Nat.even_or_odd N with he | ho
  · have hh := literal_even_disk_pairProduct_bound N hN he hr.le hr1 x y
      (fun i => (hx i).le) (fun i => (hy i).le)
    have hdiv : N - N / 2 = N / 2 := by obtain ⟨n, hn⟩ := he; omega
    rw [hdiv]
    calc
      _ ≤ literalContourKernelBound r ^ N * (N : ℝ) ^ (N / 2) := hh
      _ ≤ literalContourPairBound r ^ N * (N : ℝ) ^ (N / 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 hCK N) (by positivity)
      _ ≤ _ := by
        nlinarith [mul_nonneg (pow_nonneg (hC0.trans hCK) N) (pow_nonneg (Nat.cast_nonneg N) (N / 2))]
  · have hh := literal_odd_circle_pairProduct_bound N ho hr.le hr1 x y hx hy
    have hk : (N + 1) / 2 = N - N / 2 := by obtain ⟨n, hn⟩ := ho; omega
    rw [hk] at hh
    have hn : (N + 1 : ℝ) ≤ 2 * N := by
      have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hp : (N + 1 : ℝ) ^ (N - N / 2) ≤ 2 ^ N * (N : ℝ) ^ (N - N / 2) := by
      calc
        _ ≤ (2 * (N : ℝ)) ^ (N - N / 2) := pow_le_pow_left₀ (by positivity) hn _
        _ = 2 ^ (N - N / 2) * (N : ℝ) ^ (N - N / 2) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le N (N / 2))) (by positivity)
    apply (mul_le_mul_iff_right₀ (pow_pos hr (2 * N))).mp
    calc
      _ ≤ literalContourKernelBound r ^ (N + 1) * (N + 1 : ℝ) ^ (N - N / 2) := hh
      _ ≤ literalContourKernelBound r ^ (N + 1) * (2 ^ N * (N : ℝ) ^ (N - N / 2)) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hC0 _)
      _ = _ := by
        unfold literalContourPairBound
        rw [div_pow, mul_pow, pow_succ, pow_mul]
        field_simp

end
end IsingBulk.AnisoF002.RegularTail.C03
