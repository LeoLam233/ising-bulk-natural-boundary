import IsingBulk.HT22.Geometry.WholeTorus
import IsingBulk.Preferred22.ContourJacobianRestriction
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators ContDiff

def signedDerivativeJacobian {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => -Complex.I *
    (fderiv ℝ (signedParameterHomotopy a τ p m) (Fin.cons lam θ) (Pi.single i.succ 1)) j

def signedShiftEntry {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) (q j : Fin n) : ℝ :=
  let a := signedAngles a θ
  τ/(n+1) * ((if j=q then occupancy p a*deriv m (θ j) -
    occupancy m a*deriv p (θ j) else 0) +
    m (θ j)*(deriv p (θ q)-deriv p (a (Fin.last n))) -
    p (θ j)*(deriv m (θ q)-deriv m (a (Fin.last n))))

theorem signedAngles_update_hasDerivAt {n : ℕ} (a : ℝ) (θ : Fin n → ℝ) (q : Fin n) :
    HasDerivAt (fun t => signedAngles a (Function.update θ q t))
      (Fin.snoc (Pi.single q 1) (-1)) (θ q) := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedAngles, Fin.snoc_last]
    have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j)).const_sub a
    convert! hh using 1
    simp
  · simp only [signedAngles, Fin.snoc_castSucc]
    exact hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j

theorem signedShift_update_hasDerivAt {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    HasDerivAt (fun t => balancedShift τ p m
      (signedAngles a (Function.update θ q t)) j.castSucc)
      (signedShiftEntry a τ p m θ q j) (θ q) := by
  have hh := balancedShift_hasDerivAt τ p m (signedAngles_update_hasDerivAt a θ q)
    (fun l => hp _) (fun l => hm _) j.castSucc
  simp only [Function.update_eq_self] at hh
  have hs (f : ℝ → ℝ) :
      (∑ l : Fin (n+1), deriv f (signedAngles a θ l) *
        (Fin.snoc (Pi.single q 1) (-1) : Fin (n+1) → ℝ) l) =
        deriv f (θ q)-deriv f (signedAngles a θ (Fin.last n)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [signedAngles, Fin.snoc_castSucc, Fin.snoc_last,
      mul_neg, mul_one]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  rw [hs p, hs m] at hh
  convert hh using 1
  simp only [signedShiftEntry, signedAngles, Fin.snoc_castSucc]
  by_cases hj : j=q
  · subst j
    simp
    ring_nf
    simp
  · simp [hj]
    ring_nf
    simp

theorem signedDerivativeJacobian_entry {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    signedDerivativeJacobian a τ lam p m θ q j =
      (if q=j then 1 else 0) - Complex.I*(lam:ℂ)*(signedShiftEntry a τ p m θ q j:ℂ) := by
  have hH := (signedParameterHomotopy_contDiff n a τ p m hp hm).differentiable (by simp)
  have hh := (hH (Fin.cons lam θ)).hasFDerivAt.comp_hasDerivAt_of_eq (θ q)
    (hasDerivAt_update (Fin.cons lam θ) q.succ (θ q)) (by simp)
  have he : (fun t => signedParameterHomotopy a τ p m (Function.update (Fin.cons lam θ) q.succ t)) =
      fun t j => Complex.I*(Function.update θ q t j:ℂ) +
        (lam:ℂ)*(balancedShift τ p m (signedAngles a (Function.update θ q t)) j.castSucc:ℂ) := by
    funext t j
    have hq : (0:Fin (n+1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
    simp [signedParameterHomotopy, signedFreeLogHomotopy, Function.update_apply, hq]
    exact Or.inl (congrArg (fun x => balancedShift τ p m (signedAngles a x) j.castSucc)
      (by funext i; simp [Function.update_apply]))
  simp only [Function.comp_def] at hh
  rw [he] at hh
  have hl : HasDerivAt (fun t j => Complex.I*(Function.update θ q t j:ℂ) +
        (lam:ℂ)*(balancedShift τ p m (signedAngles a (Function.update θ q t)) j.castSucc:ℂ))
      (fun j => Complex.I*((Pi.single q (1:ℝ) : Fin n → ℝ) j:ℂ) +
        (lam:ℂ)*(signedShiftEntry a τ p m θ q j:ℂ)) (θ q) := by
    apply hasDerivAt_pi.mpr
    intro j
    exact ((hasDerivAt_pi.mp (hasDerivAt_update θ q (θ q)) j).ofReal_comp.const_mul
      Complex.I).add ((signedShift_update_hasDerivAt a τ p m
        (hp.differentiable (by simp)) (hm.differentiable (by simp)) θ q j).ofReal_comp.const_mul (lam:ℂ))
  have hd := congrFun (hh.unique hl) j
  unfold signedDerivativeJacobian
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

theorem signedDerivativeJacobian_entry_eq_full {n : ℕ}
    (a τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    signedDerivativeJacobian a τ lam p m θ q j =
      fullAngularJacobian τ lam p m (signedAngles a θ) j.castSucc q.castSucc -
      fullAngularJacobian τ lam p m (signedAngles a θ) j.castSucc (Fin.last n) := by
  rw [signedDerivativeJacobian_entry a τ lam p m hp hm]
  unfold fullAngularJacobian shiftJacobian signedShiftEntry occupancy
  simp only [signedAngles, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.castSucc_ne_last, ite_false, Fin.castSucc_inj]
  by_cases hqj : q=j
  · subst j
    simp only [ite_true]
    push_cast
    ring
  · simp only [hqj, Ne.symm hqj, ite_false]
    push_cast
    ring

theorem signedDerivativeJacobian_det_eq_full {n : ℕ}
    (a τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) :
    (signedDerivativeJacobian a τ lam p m θ).det =
      (fullAngularJacobian τ lam p m (signedAngles a θ)).det := by
  let A := fullAngularJacobian τ lam p m (signedAngles a θ)
  let B : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    A i.castSucc j.castSucc - A i.castSucc (Fin.last n)
  have he : signedDerivativeJacobian a τ lam p m θ = B.transpose := by
    ext q j
    exact signedDerivativeJacobian_entry_eq_full a τ lam p m hp hm θ q j
  rw [he, Matrix.det_transpose]
  exact (determinant_restrict_sum_hyperplane A
    (fullAngularJacobian_column_sum τ lam p m (signedAngles a θ))).symm

end
end IsingBulk.HT22.Physical
