import IsingBulk.Anisotropic.Algebra.SchurHadamard
import IsingBulk.Tail.ExteriorPairBridge
import IsingBulk.Anisotropic.FormFactors.ContourNorm

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

def contourKernelBound (r : ℝ) : ℝ := 2/(1-r^2)

theorem contourKernelBound_ge_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ contourKernelBound r := by
  have hd : 0 < 1-r^2 := by nlinarith
  unfold contourKernelBound
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg r]

theorem disk_pair_denominator {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {x y : ℂ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : 1-x*y ≠ 0 := by
  have hp : ‖x*y‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ r*r := mul_le_mul hx hy (norm_nonneg _) hr
      _ < 1 := by nlinarith
  intro he
  have he' : x*y=1 := by linear_combination -he
  rw [he',norm_one] at hp
  exact (lt_irrefl _) hp

theorem disk_pairKernel_norm_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {x y : ℂ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖pairKernel x y‖ ≤ contourKernelBound r := by
  have hp : ‖x*y‖ ≤ r^2 := by rw [norm_mul,pow_two]; exact mul_le_mul hx hy (norm_nonneg _) hr
  have hd : 1-r^2 ≤ ‖1-x*y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (x*y)
    norm_num at hh
    rw [norm_mul] at hp
    linarith
  have hn : ‖x-y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  unfold pairKernel contourKernelBound
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hn (by nlinarith) hd

theorem even_disk_pairProduct_bound (N : ℕ) (hN : 0 < N) (hEven : Even N)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖≤r) (hy : ∀ i, ‖y i‖≤r) :
    ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤
      (contourKernelBound r)^N*(N:ℝ)^(N/2) := by
  obtain ⟨n,hn⟩ := hEven
  have he : N=2*n := by omega
  clear hn
  subst N
  rw [pairProduct_eq_schur,pairProduct_eq_schur]
  have hh := Algebra.even_double_pairProduct_bound (by omega : 0<n) x y
    (fun i j => disk_pair_denominator hr hr1 (hx i) (hx j))
    (fun i j => disk_pair_denominator hr hr1 (hy i) (hy j))
    (show 0 ≤ contourKernelBound r from le_trans zero_le_one (contourKernelBound_ge_one hr hr1))
    (fun i j => disk_pairKernel_norm_le hr hr1 (hx i) (hx j))
    (fun i j => disk_pairKernel_norm_le hr hr1 (hy i) (hy j))
  convert hh using 1 <;> norm_num
  rfl

theorem pairProduct_cons_zero_norm (N : ℕ) {r : ℝ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=r) :
    ‖First.pairProduct (Fin.cons 0 x)‖ = r^N*‖First.pairProduct x‖ := by
  rw [pairProduct_eq_schur,pairProduct_eq_schur,List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Schur.pairProduct,List.map_ofFn,List.prod_ofFn]
  simp only [Function.comp_apply,pairKernel,zero_sub,zero_mul,sub_zero,div_one,norm_mul,norm_prod,norm_neg,hx,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Odd particle numbers are genuinely controlled by adjoining a zero
coordinate. Its r^N factor is retained, never replaced by a fictitious bound. -/
theorem odd_circle_pairProduct_bound (N : ℕ) (hOdd : Odd N)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=r) (hy : ∀ i, ‖y i‖=r) :
    r^(2*N)*(‖First.pairProduct x‖*‖First.pairProduct y‖) ≤
      (contourKernelBound r)^(N+1)*(N+1:ℝ)^((N+1)/2) := by
  have heven : Even (N+1) := by exact hOdd.add_odd (by decide : Odd 1)
  have hh := even_disk_pairProduct_bound (N+1) (by omega) heven hr hr1 (Fin.cons 0 x) (Fin.cons 0 y)
    (fun i => Fin.cases (by simpa using hr) (fun j => (hx j).le) i)
    (fun i => Fin.cases (by simpa using hr) (fun j => (hy j).le) i)
  rw [pairProduct_cons_zero_norm N x hx,pairProduct_cons_zero_norm N y hy] at hh
  convert hh using 1 <;> push_cast <;> ring

def contourPairBound (r : ℝ) : ℝ := 2*contourKernelBound r/r^2

theorem circle_pairProduct_bound (N : ℕ) (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=r) (hy : ∀ i, ‖y i‖=r) :
    ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤
      contourKernelBound r*(contourPairBound r)^N*(N:ℝ)^(N-N/2) := by
  have hC := contourKernelBound_ge_one hr.le hr1
  have hC0 : 0 ≤ contourKernelBound r := le_trans zero_le_one hC
  have hCK : contourKernelBound r ≤ contourPairBound r := by
    unfold contourPairBound
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    have hsq : r^2 ≤ 1 := by nlinarith
    nlinarith
  rcases Nat.even_or_odd N with he | ho
  · have hh := even_disk_pairProduct_bound N hN he hr.le hr1 x y (fun i => (hx i).le) (fun i => (hy i).le)
    have hdiv : N-N/2=N/2 := by obtain ⟨n,hn⟩ := he; omega
    rw [hdiv]
    calc
      _ ≤ (contourKernelBound r)^N*(N:ℝ)^(N/2) := hh
      _ ≤ (contourPairBound r)^N*(N:ℝ)^(N/2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 hCK N) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (hC0.trans hCK) N) (pow_nonneg (Nat.cast_nonneg N) (N/2))]
  · have hh := odd_circle_pairProduct_bound N ho hr.le hr1 x y hx hy
    have hk : (N+1)/2=N-N/2 := by obtain ⟨n,hn⟩ := ho; omega
    rw [hk] at hh
    have hn : (N+1:ℝ) ≤ 2*N := by
      have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hkN : N-N/2 ≤ N := Nat.sub_le _ _
    have hpow : (N+1:ℝ)^(N-N/2) ≤ 2^N*(N:ℝ)^(N-N/2) := by
      calc
        _ ≤ (2*(N:ℝ))^(N-N/2) := pow_le_pow_left₀ (by positivity) hn _
        _ = 2^(N-N/2)*(N:ℝ)^(N-N/2) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkN) (by positivity)
    apply (mul_le_mul_iff_right₀ (pow_pos hr (2*N))).mp
    calc
      _ ≤ (contourKernelBound r)^(N+1)*(N+1:ℝ)^(N-N/2) := hh
      _ ≤ (contourKernelBound r)^(N+1)*(2^N*(N:ℝ)^(N-N/2)) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hC0 _)
      _ = _ := by
        unfold contourPairBound
        rw [div_pow,mul_pow,pow_succ,pow_mul]
        field_simp
end
end IsingBulk.Anisotropic.FormFactors
