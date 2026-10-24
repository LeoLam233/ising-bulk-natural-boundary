import IsingBulk.Anisotropic.Algebra.SchurElimination

namespace IsingBulk.Anisotropic.Algebra
noncomputable section
open Matrix

def skewPivot (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,k;-k,0]
def skewPivotInverse (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,-k⁻¹;k⁻¹,0]

theorem skewPivotInverse_mul {k : ℂ} (hk : k ≠ 0) :
    skewPivotInverse k * skewPivot k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewPivot,skewPivotInverse,Matrix.mul_apply,Fin.sum_univ_two,hk]

theorem det_skewPivot (k : ℂ) : (skewPivot k).det = k^2 := by
  simp [skewPivot,Matrix.det_fin_two]
  ring

theorem det_skew_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℂ) (hk : k ≠ 0) (B : Matrix (Fin 2) ι ℂ)
    (C : Matrix ι (Fin 2) ℂ) (D : Matrix ι ι ℂ) :
    (Matrix.fromBlocks (skewPivot k) B C D).det =
      k^2 * (D-C*skewPivotInverse k*B).det := by
  let : Invertible (skewPivot k) :=
    invertibleOfLeftInverse _ _ (skewPivotInverse_mul hk)
  rw [Matrix.det_fromBlocks₁₁,det_skewPivot]
  rfl

def schurTop {ι : Type*} (a b : ℂ) (v : ι → ℂ) : Matrix (Fin 2) ι ℂ :=
  fun i j => if i = 0 then schurKernel a (v j) else schurKernel b (v j)

def schurBottom {ι : Type*} (a b : ℂ) (v : ι → ℂ) : Matrix ι (Fin 2) ℂ :=
  fun i j => if j = 0 then -schurKernel a (v i) else -schurKernel b (v i)

def schurMatrix {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => schurKernel (v i) (v j)

theorem schur_complement_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℂ) (v : ι → ℂ) (hab : a ≠ b) (dab : 1-a*b ≠ 0)
    (ha : ∀ i, 1-a*v i ≠ 0) (hb : ∀ i, 1-b*v i ≠ 0)
    (hv : ∀ i j, 1-v i*v j ≠ 0) :
    schurMatrix v - schurBottom a b v * skewPivotInverse (schurKernel a b) * schurTop a b v =
    Matrix.diagonal (fun i => schurKernel a (v i)*schurKernel b (v i)) *
      schurMatrix v * Matrix.diagonal (fun i => schurKernel a (v i)*schurKernel b (v i)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    schurBottom,schurTop,skewPivotInverse,schurMatrix]
  have h := schurKernel_elimination a b (v i) (v j) hab dab (ha i) (ha j) (hb i) (hb j) (hv i j)
  convert h using 1
  ring

theorem det_schur_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℂ) (v : ι → ℂ) (hab : a ≠ b) (dab : 1-a*b ≠ 0)
    (ha : ∀ i, 1-a*v i ≠ 0) (hb : ∀ i, 1-b*v i ≠ 0)
    (hv : ∀ i j, 1-v i*v j ≠ 0) :
    (Matrix.fromBlocks (skewPivot (schurKernel a b))
      (schurTop a b v) (schurBottom a b v) (schurMatrix v)).det =
    schurKernel a b ^ 2 * (∏ i, schurKernel a (v i)*schurKernel b (v i))^2 *
      (schurMatrix v).det := by
  rw [det_skew_block _ (schurKernel_ne_zero hab dab),
    schur_complement_matrix a b v hab dab ha hb hv,
    Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
  ring

end
end IsingBulk.Anisotropic.Algebra
