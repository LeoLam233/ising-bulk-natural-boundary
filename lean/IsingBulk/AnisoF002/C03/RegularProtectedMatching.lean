import IsingBulk.AnisoF002.C03.RegularIsotropicProtectedRoots

/-!
# Complete matching on the actual protected disk

The unmatched Schur product pays one bounded factor on the entire
rho/N^6 disk. The only population cost is the proved product of vertex
weights; every angular collision and both particle parities remain.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology BigOperators
open IsingBulk.AnisoF002.Isotropic

theorem smallSchurGrowth_pow_le {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : k ≤ N ^ 2) :
    (1 + 1 / (N : ℝ) ^ 2) ^ k ≤ Real.exp 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply one_add_pow_le_exp_one (by positivity) k
  have hk' : (k : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_right hk' (by positivity : 0 ≤ 1 / (N : ℝ) ^ 2)
  simpa only [mul_one_div, div_self (pow_ne_zero 2 hN0.ne')] using hh

theorem filled_pairs_all_weighted_bound {N : ℕ} (hN : 0 < N) (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0) (v : Fin N → ℝ) (hv : ∀ i, 1 ≤ v i)
    {C : ℝ} (hC : 1 ≤ C)
    (hK : ∀ i j, ‖schur (r i) (r j)‖ ≤ 1 + 1 / (N : ℝ) ^ 2)
    (hP : ∀ i j, ‖canceledPair B (r i) (r j) (y i) (y j)‖ ≤ C * v i * v j) :
    ‖∏ ij ∈ indexPairs N, canceledPair B (r ij.1) (r ij.2) (y ij.1) (y ij.2)‖ ≤
      (matchingNumber ((N + 1) / 2) : ℝ) * C ^ N * Real.exp 1 * ∏ i, v i := by
  have hvpos (i) : 0 < v i := zero_lt_one.trans_le (hv i)
  have hvprod : 0 ≤ ∏ i, v i := Finset.prod_nonneg (fun i _ => (hvpos i).le)
  obtain ⟨n, heven | hodd⟩ := Nat.even_or_odd' N
  · subst N
    have hb := filled_pairs_even_weighted_bound A B r y hy hp hd v hvpos
      (q := 1 + 1 / ((2 * n : ℕ) : ℝ) ^ 2) (by positivity) (zero_le_one.trans hC) hK hP
      n (List.ofFn id) (by simp)
    simp only [pairProductOn_indexPairs, id_eq, List.map_ofFn, List.prod_ofFn, Function.comp_def] at hb
    have he : (2 * n + 1) / 2 = n := by omega
    rw [he]
    apply hb.trans
    have hqp := smallSchurGrowth_pow_le hN (2 * n * (n - 1)) (by nlinarith [Nat.mul_le_mul_left (2 * n) (Nat.sub_le n 1)] : 2 * n * (n - 1) ≤ (2 * n) ^ 2)
    have hcp := pow_le_pow_right₀ hC (show n ≤ 2 * n by omega)
    gcongr
  · subst N
    have hb := filled_pairs_odd_weighted_bound A B r y hy hp hd v hv
      (q := 1 + 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) (le_add_of_nonneg_right (by positivity)) hC hK hP
      n (List.ofFn id) (by simp)
    simp only [pairProductOn_indexPairs, id_eq, List.map_ofFn, List.prod_ofFn, Function.comp_def] at hb
    have he : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [he]
    apply hb.trans
    have hqp := smallSchurGrowth_pow_le hN (2 * (n + 1) * n) (by nlinarith : 2 * (n + 1) * n ≤ (2 * n + 1) ^ 2)
    have hcp := pow_le_pow_right₀ hC (show n + 1 ≤ 2 * n + 1 by omega)
    gcongr

end
end IsingBulk.AnisoF002.RegularTail.C03

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

theorem ActualMixedRootControl.continued_pair_bound {α b η τ δ : ℝ}
    (d : ActualMixedRootControl α b η τ δ) {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {z : ℂ} (hz : ‖z‖ ≤ d.radius / (N : ℝ) ^ 6) :
    ‖∏ ij ∈ indexPairs N, canceledPair 1
      (mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z ij.1)
      (mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z ij.2)
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.1 * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.2 * Complex.I))‖ ≤
      (matchingNumber ((N + 1) / 2) : ℝ) * (16 * d.pairConstant) ^ N *
        Real.exp 1 * Real.exp ((N : ℝ) / 2) := by
  let S := isotropicRadialParameter α ε
  let w := actualHomotopyAngle η τ 1 θ
  let r : Fin N → ℂ := fun i => isotropicInteriorRoot (S, w i)
  let R := mixedContinuedRoots S η τ θ z
  let v := mixedVertexWeight (mixedCosBranchCoordinates b d.beta θ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, hR, hhalf, hK, _⟩ := d.disk_bounds N hN ε hε hεδ θ hP hQ z hz
  have hold (i j : Fin N) : 1 - r i * r j ≠ 0 :=
    norm_pos_iff.mp ((div_pos d.pairGap_pos hN0).trans_le (d.center_gap N hN ε hε hεδ θ hP hQ i j))
  have hd (i j : Fin N) : 1 - R i * R j ≠ 0 :=
    norm_pos_iff.mp ((half_pos (norm_pos_iff.mpr (hold i j))).trans_le (hhalf i j))
  have hp (i : Fin N) : R i ^ 2 - 2 *
      (S + z - 1 * (Complex.exp (w i * Complex.I) + (Complex.exp (w i * Complex.I))⁻¹) / 2) * R i + 1 = 0 := by
    have hh := reciprocalRootContinuation_polynomial
      (isotropicInteriorRoot_polynomial (S, w i))
      (reciprocalRootContinuation_simple (isotropicInteriorRoot_polynomial (S, w i)) (hold i i))
      (isotropicDispersion (S, w i) + z)
    rw [one_mul, complex_cos_exp_inverse]
    convert hh using 1
    dsimp [R, mixedContinuedRoots, continuedRoots, S, w, isotropicDispersion]
    ring
  have hbound (i j : Fin N) : ‖canceledPair 1 (R i) (R j)
      (Complex.exp (w i * Complex.I)) (Complex.exp (w j * Complex.I))‖ ≤
      (16 * d.pairConstant) * v i * v j := by
    have hh := canceledPair_relative_bound (B := 1)
      (y := Complex.exp (w i * Complex.I)) (v := Complex.exp (w j * Complex.I)) (hR i) (hR j) (hhalf i j) (hold i j)
      (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    have hp' := mul_le_mul_of_nonneg_left (d.center_pair N hN ε hε hεδ θ i j) (by norm_num : (0 : ℝ) ≤ 16)
    apply hh.trans
    convert hp' using 1
    ring
  have hb := filled_pairs_all_weighted_bound hN (S + z) 1 R (fun i => Complex.exp (w i * Complex.I))
    (fun _ => Complex.exp_ne_zero _) hp hd v (fun i => mixedVertexWeight_ge_one _ i)
    (by linarith [d.pairConstant_ge_one] : 1 ≤ 16 * d.pairConstant) hK hbound
  apply hb.trans
  exact mul_le_mul_of_nonneg_left (mixedVertexWeight_total_cost _)
    (by positivity [d.pairConstant_ge_one])

end
end IsingBulk.AnisoF002.Isotropic
