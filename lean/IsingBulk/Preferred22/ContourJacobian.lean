import IsingBulk.Preferred22.ContourDeformation
import IsingBulk.Preferred22.ContourMatrix
import IsingBulk.Anisotropic.Algebra.DeterminantBound
import Mathlib.Analysis.Complex.RealDeriv

/-! Actual derivatives and uniform bounds for the balanced constrained Jacobian.
The determinant estimate uses the proper Gram-matrix inequality, with the
source-specific diagonal-plus-O(1/N) entry structure. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set

theorem balancedShift_hasDerivAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    {x : ℝ → Fin N → ℝ} {v : Fin N → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t)
    (hp : ∀ j, DifferentiableAt ℝ p (x t j))
    (hm : ∀ j, DifferentiableAt ℝ m (x t j)) (i : Fin N) :
    HasDerivAt (fun u => balancedShift τ p m (x u) i)
      (τ/N * (((∑ j, deriv p (x t j)*v j)*m (x t i) +
        occupancy p (x t)*(deriv m (x t i)*v i)) -
        ((∑ j, deriv m (x t j)*v j)*p (x t i) +
        occupancy m (x t)*(deriv p (x t i)*v i)))) t := by
  have hxi j := hasDerivAt_pi.mp hx j
  have hpj j := (hp j).hasDerivAt.comp t (hxi j)
  have hmj j := (hm j).hasDerivAt.comp t (hxi j)
  exact (((HasDerivAt.fun_sum (fun j _ => hpj j)).mul (hmj i)).sub
    ((HasDerivAt.fun_sum (fun j _ => hmj j)).mul (hpj i))).const_mul _

def constrainedShiftEntry {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) (q j : Fin n) : ℝ :=
  let a := constrainedAngles θ
  τ/(n+1) * ((if j=q then occupancy p a*deriv m (θ j) -
    occupancy m a*deriv p (θ j) else 0) +
    m (θ j)*(deriv p (θ q)-deriv p (a (Fin.last n))) -
    p (θ j)*(deriv m (θ q)-deriv m (a (Fin.last n))))

theorem constrainedAngles_update_hasDerivAt {n : ℕ} (θ : Fin n → ℝ) (q : Fin n) :
    HasDerivAt (fun t => constrainedAngles (Function.update θ q t))
      (Fin.snoc (Pi.single q 1) (-1)) (θ q) := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAngles, Fin.snoc_last]
    have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j)).neg
    convert! hh using 1
    simp
  · simp only [constrainedAngles, Fin.snoc_castSucc]
    exact hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j

theorem constrainedShift_update_hasDerivAt {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    HasDerivAt (fun t => balancedShift τ p m
      (constrainedAngles (Function.update θ q t)) j.castSucc)
      (constrainedShiftEntry τ p m θ q j) (θ q) := by
  have hh := balancedShift_hasDerivAt τ p m (constrainedAngles_update_hasDerivAt θ q)
    (fun l => hp _) (fun l => hm _) j.castSucc
  simp only [Function.update_eq_self] at hh
  have hs (f : ℝ → ℝ) :
      (∑ l : Fin (n+1), deriv f (constrainedAngles θ l) *
        (Fin.snoc (Pi.single q 1) (-1) : Fin (n+1) → ℝ) l) =
        deriv f (θ q)-deriv f (constrainedAngles θ (Fin.last n)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [constrainedAngles, Fin.snoc_castSucc, Fin.snoc_last,
      mul_neg, mul_one]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  rw [hs p, hs m] at hh
  convert hh using 1
  simp only [constrainedShiftEntry, constrainedAngles, Fin.snoc_castSucc]
  by_cases hj : j=q
  · subst j
    simp
    ring_nf
    simp
  · simp [hj]
    ring_nf
    simp

theorem constrainedAngularJacobian_entry {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    constrainedAngularJacobian τ lam p m θ q j =
      (if q=j then 1 else 0) - Complex.I*(lam:ℂ)*(constrainedShiftEntry τ p m θ q j:ℂ) := by
  have hH := (parameterHomotopy_contDiff n τ p m hp hm).differentiable (by simp)
  have hh := (hH (Fin.cons lam θ)).hasFDerivAt.comp_hasDerivAt_of_eq (θ q)
    (hasDerivAt_update (Fin.cons lam θ) q.succ (θ q)) (by simp)
  have he : (fun t => parameterHomotopy τ p m (Function.update (Fin.cons lam θ) q.succ t)) =
      fun t j => Complex.I*(Function.update θ q t j:ℂ) +
        (lam:ℂ)*(balancedShift τ p m (constrainedAngles (Function.update θ q t)) j.castSucc:ℂ) := by
    funext t j
    have hq : (0:Fin (n+1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
    simp [parameterHomotopy, freeLogHomotopy, Function.update_apply, hq]
    exact Or.inl (congrArg (fun x => balancedShift τ p m (constrainedAngles x) j.castSucc)
      (by funext i; simp [Function.update_apply]))
  simp only [Function.comp_def] at hh
  rw [he] at hh
  have hl : HasDerivAt (fun t j => Complex.I*(Function.update θ q t j:ℂ) +
        (lam:ℂ)*(balancedShift τ p m (constrainedAngles (Function.update θ q t)) j.castSucc:ℂ))
      (fun j => Complex.I*((Pi.single q (1:ℝ) : Fin n → ℝ) j:ℂ) +
        (lam:ℂ)*(constrainedShiftEntry τ p m θ q j:ℂ)) (θ q) := by
    apply hasDerivAt_pi.mpr
    intro j
    exact ((hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j).ofReal_comp.const_mul
      Complex.I).add ((constrainedShift_update_hasDerivAt τ p m
        (hp.differentiable (by simp)) (hm.differentiable (by simp)) θ q j).ofReal_comp.const_mul (lam:ℂ))
  have hd := congrFun (hh.unique hl) j
  unfold constrainedAngularJacobian
  rw [hd]
  by_cases hqj : q=j
  · subst j
    simp only [Pi.single_eq_same, Complex.ofReal_one, mul_one, ite_true]
    rw [mul_add]
    simp only [neg_mul, Complex.I_mul_I, neg_neg]
    ring
  · simp only [Pi.single_eq_of_ne (Ne.symm hqj), Complex.ofReal_zero, mul_zero,
      zero_add, hqj, ite_false, zero_sub]
    ring

theorem norm_det_le_column_l1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖A.det‖ ≤ C^n := by
  by_cases hn : n=0
  · subst n
    simp
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  have hnr : (0:ℝ)<n := by exact_mod_cast hn0
  have ht : (A.conjTranspose*A).trace.re ≤ (n:ℝ)*C^2 := by
    rw [IsingBulk.Anisotropic.Algebra.gram_trace_re]
    calc
      _ ≤ ∑ j : Fin n, C^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (A i j))).trans
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => norm_nonneg (A i j))) (hA j) 2)
      _ = _ := by simp
  have hm : (A.conjTranspose*A).trace.re / (n:ℝ) ≤ C^2 :=
    (div_le_iff₀ hnr).mpr (by simpa [mul_comm] using ht)
  have hg : 0≤(A.conjTranspose*A).trace.re / (n:ℝ) := by
    rw [IsingBulk.Anisotropic.Algebra.gram_trace_re]
    positivity
  have hd0 := IsingBulk.Anisotropic.Algebra.norm_det_sq_le_trace_mean_pow A
    (by simpa using hn0)
  simp only [Fintype.card_fin] at hd0
  have hd := hd0.trans (pow_le_pow_left₀ hg hm n)
  have he : (C^2)^n=(C^n)^2 := by rw [←pow_mul,←pow_mul];congr 1;omega
  rw [he] at hd
  nlinarith [norm_nonneg A.det, pow_nonneg hC n]

end
end IsingBulk.Preferred22
