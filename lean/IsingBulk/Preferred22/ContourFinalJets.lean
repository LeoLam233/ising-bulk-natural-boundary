import IsingBulk.Preferred22.ContourJetBounds

/-! The fixed-jet clause of LT22 Lemma 5.1 for the actual constrained angular
Jacobian. Constants are chosen before particle number; the bound is C^N N^(2J). -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def constrainedAnglesCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.lastCases (-∑ i, ContinuousLinearMap.proj i)
    (fun i => ContinuousLinearMap.proj i))

@[simp] theorem constrainedAnglesCLM_apply (n : ℕ) (θ : Fin n → ℝ) :
    constrainedAnglesCLM n θ = constrainedAngles θ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [constrainedAnglesCLM, constrainedAngles]
  · simp [constrainedAnglesCLM, constrainedAngles]

theorem constrainedAnglesCLM_norm_le (n : ℕ) :
    ‖constrainedAnglesCLM n‖ ≤ (n+1:ℕ) := by
  apply (constrainedAnglesCLM n).opNorm_le_bound (Nat.cast_nonneg _)
  intro θ
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg θ))).mpr
  intro i
  rw [constrainedAnglesCLM_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAngles, Fin.snoc_last, norm_neg]
    calc
      _ ≤ ∑ j, ‖θ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, ‖θ‖ := Finset.sum_le_sum (fun j _ => norm_le_pi_norm θ j)
      _ ≤ ((n+1:ℕ):ℝ)*‖θ‖ := by simp; nlinarith [norm_nonneg θ]
  · simp only [constrainedAngles, Fin.snoc_castSucc]
    exact (norm_le_pi_norm θ j).trans (by
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [norm_nonneg θ, Nat.cast_nonneg (α := ℝ) n])

/-- All fixed jets of the concrete constrained determinant, uniformly in N. -/
theorem constrainedAngularJacobian_uniform_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ lam : ℝ) (J : ℕ) : ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (θ : Fin n → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (constrainedAngularJacobian τ lam p m x).det) θ‖ ≤
          C^(n+1)*((n+1:ℕ):ℝ)^(2*r) := by
  obtain ⟨C,hC,hbound⟩ := fullAngularJacobian_determinant_uniform_jets p m hp hm hpp hmp τ lam J
  refine ⟨C,hC,?_⟩
  intro n θ r hr
  let L := constrainedAnglesCLM n
  let f : (Fin (n+1) → ℝ) → ℂ := fun x => (fullAngularJacobian τ lam p m x).det
  have hf : ContDiff ℝ ∞ f := fullAngularJacobian_det_contDiff τ lam p m hp hm
  have he : (fun x : Fin n → ℝ => (constrainedAngularJacobian τ lam p m x).det) = f ∘ L := by
    funext x
    simpa only [Function.comp_apply, L, constrainedAnglesCLM_apply, f] using
      constrainedAngularJacobian_det_eq_full τ lam p m hp hm x
  rw [he, L.iteratedFDeriv_comp_right hf θ (by simp)]
  apply ((iteratedFDeriv ℝ r f (L θ)).norm_compContinuousLinearMap_le _).trans
  have hprod : (∏ _k : Fin r, ‖L‖) ≤ ((n+1:ℕ):ℝ)^r := by
    simpa using Finset.prod_le_prod₀ (fun _ (_ : _∈(Finset.univ : Finset (Fin r))) => norm_nonneg L)
      (fun _ (_ : _∈(Finset.univ : Finset (Fin r))) => constrainedAnglesCLM_norm_le n)
  have hfbound := hbound (n+1) (by omega) (L θ) r hr
  calc
    _ ≤ (C^(n+1)*((n+1:ℕ):ℝ)^r)*((n+1:ℕ):ℝ)^r :=
      mul_le_mul hfbound hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg L)) (by positivity)
    _ = _ := by rw [two_mul, pow_add]; ring

theorem constrainedAngularJacobian_fixed_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ lam : ℝ) (J : ℕ) : ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (θ : Fin n → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (constrainedAngularJacobian τ lam p m x).det) θ‖ ≤
          C^(n+1)*((n+1:ℕ):ℝ)^(2*J) := by
  obtain ⟨C,hC,hbound⟩ := constrainedAngularJacobian_uniform_jets p m hp hm hpp hmp τ lam J
  refine ⟨C,hC,?_⟩
  intro n θ r hr
  exact (hbound n θ r hr).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_cast; omega) (Nat.mul_le_mul_left 2 hr)) (by positivity))

end
end IsingBulk.Preferred22
