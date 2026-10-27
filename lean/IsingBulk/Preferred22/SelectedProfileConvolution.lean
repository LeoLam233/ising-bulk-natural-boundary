import IsingBulk.Preferred22.SelectedProfileMass

/-! The actual selected-sector independent angular profile has a uniform
complete constrained product bound at every particle order N>=4. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

/-- Genuine integrability, including the actual last constrained angle. -/
theorem preferred_selected_profile_product_integrable (d : PreferredBranchData)
    (n : ℕ) {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun θ : Fin n → ℝ =>
      ∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε (constrainedAngles θ i)) (angularBox n) := by
  have hf := preferred_selected_oneBody_profile_continuous d hε
  have hc : Continuous (fun θ : Fin n → ℝ =>
      ∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε (constrainedAngles θ i)) := by
    apply continuous_finsetProd
    intro i _
    exact hf.comp ((continuous_apply i).comp (constrainedAngles_continuous n))
  have hh : IntegrableOn (fun θ : Fin n → ℝ =>
      ∏ i : Fin (n+1),preferredSelectedOneBodyProfile d ε (constrainedAngles θ i))
      (Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi)) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  apply hh.mono_set
  intro θ hθ
  have ht : ∀i,-Real.pi<θ i ∧ θ i≤Real.pi := by simpa [angularBox] using hθ
  exact ⟨fun i => (ht i).1.le,fun i => (ht i).2⟩

/-- Exact all-N form used in the physical selected derivative assembly.
The constant is chosen before both N and the positive regularization. -/
theorem preferred_selected_profile_constrained_mass (d : PreferredBranchData) :
    ∃C>0,∀n : ℕ,4≤n+1→∀ε>0,
      (∫ θ in angularBox n,∏ i : Fin (n+1),
        preferredSelectedOneBodyProfile d ε (constrainedAngles θ i))≤C^(n+1) := by
  obtain ⟨A,hA,hbound⟩ := preferred_selected_profile_uniform_mass d
  let C := max 1 A
  have hC1 : 1≤C := le_max_left _ _
  have hC : 0<C := lt_of_lt_of_le zero_lt_one hC1
  have hAC : A≤C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro n hn ε hε
  obtain ⟨m,rfl⟩ : ∃m : ℕ,n=m+3 := ⟨n-3,by omega⟩
  have hf := preferred_selected_oneBody_profile_continuous d hε
  have hnonneg (θ : ℝ) : 0≤preferredSelectedOneBodyProfile d ε θ :=
    (preferred_selected_oneBody_profile_pos d hε θ).le
  have h := preferred_angularBox_four_thirds_bound hf
    (preferred_selected_oneBody_profile_periodic d ε) hnonneg m
  have hfour : 0≤∫ θ in Ioc (-Real.pi) Real.pi,
      (preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ) :=
    integral_nonneg (fun θ => Real.rpow_nonneg (hnonneg θ) _)
  have hone : 0≤∫ θ in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε θ :=
    integral_nonneg hnonneg
  have hpow := mul_le_mul
    (pow_le_pow_left₀ hfour ((hbound ε hε).1.trans hAC) 3)
    (pow_le_pow_left₀ hone ((hbound ε hε).2.trans hAC) m)
    (pow_nonneg hone m) (pow_nonneg hC.le 3)
  have he : C^3*C^m=C^(m+3) := by rw [pow_add]; ring
  exact h.trans (hpow.trans (he.le.trans (pow_le_pow_right₀ hC1 (by omega))))

/-- A fixed pointwise prefactor remains an honest exponential in N. -/
theorem preferred_selected_profile_scaled_mass (d : PreferredBranchData) :
    ∃C>0,∀A : ℝ,0≤A→∀n : ℕ,4≤n+1→∀ε>0,
      (∫ θ in angularBox n,∏ i : Fin (n+1),
        A*preferredSelectedOneBodyProfile d ε (constrainedAngles θ i))≤(A*C)^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := preferred_selected_profile_constrained_mass d
  refine ⟨C,hC,?_⟩
  intro A hA n hn ε hε
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [integral_const_mul,mul_pow]
  exact mul_le_mul_of_nonneg_left (hbound n hn ε hε) (pow_nonneg hA _)

end
end IsingBulk.Preferred22
