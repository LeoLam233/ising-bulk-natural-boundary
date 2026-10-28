import IsingBulk.HT22.Anchor.Normalization
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Genuine odd bordered amplitude jets. The extra N comes from the ghost
border, not a hidden factorial or radial constant. -/
theorem actual_amplitude_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2) (s,q) ∧
      ∀ j≤J,‖iteratedFDeriv ℂ j
        (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2) (s,q)‖≤
        (C/Real.sqrt N)^N*(N:ℝ)^(J+1) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_amplitude_normalized_balls d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,c,A,H,hε₀,hτ₀,hc,hA,hH,hball⟩ := hsource B hB δB hδB
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro J
  let D := fun j : ℕ => cauchyJetConstant j*H/c^j
  have hD (j : ℕ) : 0<D j := by dsimp [D]; exact div_pos (mul_pos (cauchyJetConstant_pos j) hH) (pow_pos hc j)
  let M := 1+∑ j∈Finset.range (J+1),D j
  have hM : 1≤M := by
    have hh := Finset.sum_nonneg (fun j (_ : j∈Finset.range (J+1)) => (hD j).le)
    dsimp [M]
    linarith
  have hDM (j : ℕ) (hj : j≤J) : D j≤M := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => (hD k).le)
      (show j∈Finset.range (J+1) by simp; omega)
    dsimp [M]
    linarith
  let C := max 1 A*M
  have hC : 1≤C := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hM
  refine ⟨C,hC,?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hr : 0<c/(N:ℝ) := div_pos hc hNr
  obtain ⟨F,heq,hFa,hFb⟩ := hball N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor
  have hFat : AnalyticAt ℂ F (s,q) := hFa _ (mem_closedBall_self hr.le)
  refine ⟨hFat.congr heq.symm,?_⟩
  intro j hj
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := analytic_iteratedFDeriv_center_bound F (s,q) (c/(N:ℝ)) (H*(A/Real.sqrt N)^N*(N:ℝ)) hr
    (hFa.mono ball_subset_closedBall) (fun z hz => hFb z (ball_subset_closedBall hz)) j
  have hid : cauchyJetConstant j*(H*(A/Real.sqrt N)^N*(N:ℝ))/(c/(N:ℝ))^j=
      D j*(A/Real.sqrt N)^N*(N:ℝ)^(j+1) := by
    dsimp only [D]
    simp only [div_pow,pow_succ]
    field_simp [hc.ne',hNr.ne',hsqrt.ne']
  rw [hid] at hh
  have hDMN : D j≤M^N := (hDM j hj).trans (le_self_pow₀ hM hN.ne')
  calc
    _ ≤ D j*(A/Real.sqrt N)^N*(N:ℝ)^(j+1) := hh
    _ ≤ M^N*(max 1 A/Real.sqrt N)^N*(N:ℝ)^(J+1) := by
      apply mul_le_mul
      · exact mul_le_mul hDMN (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (le_max_right _ _) hsqrt.le) N) (by positivity) (by positivity)
      · exact pow_le_pow_right₀ hN1 (Nat.add_le_add_right hj 1)
      · positivity
      · positivity
    _ = _ := by
      rw [← mul_pow]
      congr 2
      dsimp [C]
      ring


end
end IsingBulk.HT22.Anchor
