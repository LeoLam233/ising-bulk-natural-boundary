import IsingBulk.Tail.RealHomogeneousInverseJets

namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

theorem RealScaledJetBound.pow {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (hρ : 0 < ρ) (m : ℕ) (hm : 1 ≤ m) :
    RealScaledJetBound (fun y => (f y)^m) x J ρ (C^m*(m:ℝ)^J) (a*(m:ℤ)) := by
  have hC := h.nonneg
  refine ⟨h.smooth.pow m,by positivity,?_⟩
  intro k hk
  have hh := smooth_finset_product_scaled_jets (Finset.univ : Finset (Fin m)) (fun _ => f)
    x J C ρ a h.nonneg hρ (fun _ _ => h.smooth) (fun _ _ => h.bound) k hk
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hm) hk) (by positivity))
    (zpow_nonneg hρ.le _))

theorem real_linear_scaled_jets (L : E →L[ℝ] ℂ) (x : E) (J : ℕ) (ρ C : ℝ)
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (hx : ‖L x‖ ≤ C*ρ) :
    RealScaledJetBound L x J ρ C 1 := by
  refine ⟨L.contDiff.contDiffAt,hC,?_⟩
  intro k hk
  cases k with
  | zero => simpa using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L=(fun _ => L) := funext (fun _ => L.fderiv)
    rw [he]
    cases k with
    | zero => simpa using hL
    | succ k =>
      simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
      exact mul_nonneg hC (zpow_nonneg hρ.le _)

theorem RealScaledJetBound.finset_sum {ι : Type*} (S : Finset ι) {f : ι → E → ℂ}
    {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : ∀ i ∈ S, RealScaledJetBound (f i) x J ρ C a) (hC : 0 ≤ C) :
    RealScaledJetBound (fun y => ∑ i ∈ S, f i y) x J ρ ((S.card:ℝ)*C) a := by
  refine ⟨ContDiffAt.sum (fun i hi => (h i hi).smooth),by positivity,?_⟩
  intro k hk
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (h i hi).smooth.of_le (by simp))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ S, C*ρ^(a-(k:ℤ)) := Finset.sum_le_sum (fun i hi => (h i hi).bound k hk)
    _ = _ := by simp [mul_assoc]

def jointAngularDifference {N : ℕ} (i j : Fin N) : (ℂ × (Fin N → ℝ)) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)-(ContinuousLinearMap.proj j)).comp
    (ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ)))

theorem jointAngularDifference_apply {N : ℕ} (i j : Fin N) (x : ℂ × (Fin N → ℝ)) :
    jointAngularDifference i j x=((x.2 i-x.2 j:ℝ):ℂ) := by
  simp [jointAngularDifference]

theorem jointAngularDifference_norm {N : ℕ} (i j : Fin N) : ‖jointAngularDifference i j‖ ≤ 2 := by
  apply (jointAngularDifference i j).opNorm_le_bound (by norm_num)
  intro x
  rw [jointAngularDifference_apply,Complex.norm_real]
  have hi := (norm_le_pi_norm x.2 i).trans (norm_snd_le x)
  have hj := (norm_le_pi_norm x.2 j).trans (norm_snd_le x)
  exact (norm_sub_le _ _).trans (by linarith)

theorem jointAngularDifference_scaled {N : ℕ} (i j : Fin N) (x : ℂ × (Fin N → ℝ))
    (J : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hx : |x.2 i-x.2 j| ≤ ρ) :
    RealScaledJetBound (fun y : ℂ × (Fin N → ℝ) => ((y.2 i-y.2 j:ℝ):ℂ)) x J ρ 2 1 := by
  have hh := real_linear_scaled_jets (jointAngularDifference i j) x J ρ 2 hρ (by norm_num)
    (jointAngularDifference_norm i j) (by
      rw [jointAngularDifference_apply,Complex.norm_real,Real.norm_eq_abs]
      linarith)
  change RealScaledJetBound (fun y => jointAngularDifference i j y) x J ρ 2 1 at hh
  simpa only [jointAngularDifference_apply] using hh

end
end IsingBulk.Tail
