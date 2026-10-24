import IsingBulk.Anisotropic.Algebra.SchurDeterminant
import IsingBulk.Anisotropic.Algebra.DeterminantBound

namespace IsingBulk.Anisotropic.Algebra
noncomputable section

theorem even_pairProduct_norm_sq_bound {n : ℕ} (hn : 0<n)
    (v : Fin (2*n) → ℂ) (hd : ∀ i j, 1-v i*v j ≠ 0)
    {C : ℝ} (hC : 0≤C) (hv : ∀ i j, ‖schurKernel (v i) (v j)‖≤C) :
    ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn v)‖^2 ≤
      (2*n:ℝ)^n * C^(2*n) := by
  let e : Fin (2*n) ≃ PairIndex n :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,card_pairIndex])
  let w : PairIndex n → ℂ := fun i => v (e.symm i)
  have hdw : ∀ i j, 1-w i*w j ≠ 0 := fun i j => hd (e.symm i) (e.symm j)
  have h := norm_det_sq_le_entry_bound (schurMatrix w) hC
    (fun i j => hv (e.symm i) (e.symm j)) (by rw [card_pairIndex]; omega)
  rw [even_schur_det w hdw,norm_pow,card_pairIndex] at h
  have heq : ‖IsingBulk.Schur.pairProduct schurKernel (pairedList w)‖ =
      ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn v)‖ := by
    simpa only [w,Equiv.symm_apply_apply] using norm_pairedList_eq_ofFn e w
  rw [heq] at h
  have hr : ((↑(2*n):ℝ)*C^2)^(2*n) = ((2*n:ℝ)^n*C^(2*n))^2 := by
    calc
      ((↑(2*n):ℝ)*C^2)^(2*n) = (((↑(2*n):ℝ)*C^2)^n)^2 := by
        rw [← pow_mul, Nat.mul_comm n 2]
      _ = _ := by
        congr 1
        rw [Nat.cast_mul,Nat.cast_ofNat,mul_pow,← pow_mul]
  rw [hr] at h
  exact (sq_le_sq₀ (sq_nonneg _) (by positivity)).mp h

theorem even_double_pairProduct_bound {n : ℕ} (hn : 0<n)
    (v w : Fin (2*n) → ℂ) (hv : ∀ i j, 1-v i*v j ≠ 0)
    (hw : ∀ i j, 1-w i*w j ≠ 0) {C : ℝ} (hC : 0≤C)
    (hvc : ∀ i j, ‖schurKernel (v i) (v j)‖≤C)
    (hwc : ∀ i j, ‖schurKernel (w i) (w j)‖≤C) :
    ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn v)‖ *
      ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn w)‖ ≤
      C^(2*n)*(2*n:ℝ)^n := by
  have h1 := even_pairProduct_norm_sq_bound hn v hv hC hvc
  have h2 := even_pairProduct_norm_sq_bound hn w hw hC hwc
  nlinarith [sq_nonneg (‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn v)‖-
    ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn w)‖)]

end
end IsingBulk.Anisotropic.Algebra
