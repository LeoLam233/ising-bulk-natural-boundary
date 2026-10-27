import IsingBulk.Preferred22.FiniteComplementMass
import IsingBulk.Preferred22.PuncturedRadialIntegral
import IsingBulk.Preferred22.RightRadialTransport

/-! Genuine fixed-radius punctured mass for every positive even particle
order. The cutoff support is quantitatively separated from full equality;
therefore the actual all-order shell estimate applies to a finite dyadic prefix. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

theorem preferredEqualitySize_le_diameter_sq {N : ℕ} (θ : Fin N → ℝ) :
    preferredEqualitySize θ≤(N:ℝ)^2*(preferredAngularDiameter θ)^2 := by
  have hp (a b : Fin N) : (θ a-θ b)^2≤(preferredAngularDiameter θ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (θ a-θ b))
      (preferredAngularDiameter_pair_le θ a b) 2
    simpa only [sq_abs] using hh
  unfold preferredEqualitySize
  calc
    _ ≤ ∑ _a : Fin N,∑ _b : Fin N,(preferredAngularDiameter θ)^2 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hp a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem preferredEqualityCutoff_zero_of_small_diameter {N : ℕ} (hN : 0<N)
    {R : ℝ} (hR : 0<R) (θ : Fin N → ℝ)
    (hd : preferredAngularDiameter θ≤R/(2*(N:ℝ))) :
    preferredEqualityCutoff R θ=0 := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hD : 0≤preferredAngularDiameter θ := Metric.diam_nonneg
  have hh := (le_div_iff₀ (by positivity : 0<2*(N:ℝ))).mp hd
  have hsq := pow_le_pow_left₀ (by positivity : 0≤preferredAngularDiameter θ*(2*(N:ℝ))) hh 2
  apply preferredPopulationCutoff_zero
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  nlinarith [preferredEqualitySize_le_diameter_sq θ]

theorem preferredEqualityCutoffPartial_zero_of_small_diameter {N : ℕ} (hN : 0<N)
    {R : ℝ} (hR : 0<R) (θ : Fin N → ℝ) (i : Fin N)
    (hd : preferredAngularDiameter θ<R/(2*(N:ℝ))) :
    preferredEqualityCutoffPartial R θ i=0 := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hD : 0≤preferredAngularDiameter θ := Metric.diam_nonneg
  have hh := (lt_div_iff₀ (by positivity : 0<2*(N:ℝ))).mp hd
  have hsq : (preferredAngularDiameter θ*(2*(N:ℝ)))^2<R^2 := by
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<R+preferredAngularDiameter θ*(2*(N:ℝ)) by positivity)]
  have hx : preferredEqualitySize θ/R^2<(1/4:ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [preferredEqualitySize_le_diameter_sq θ]
  rw [preferredEqualityCutoffPartial_formula,preferredPopulationCutoff_deriv_zero_lower hx,
    zero_mul,zero_div]

/-- This is the actual punctured physical density, including normalization
and every original occupancy/cutoff factor. -/
theorem preferredPuncturedDensity_away_domination {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ)
    (rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ) {R : ℝ} (hR : 0<R) (θ : Fin n → ℝ) :
    ENNReal.ofReal ‖preferredPuncturedDensity d B τ R rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAngles θ))‖≤
    preferredRightAwayMassIntegrand d B τ preferredPopulationCutoff rcut j ε
      (R/(2*((n+1:ℕ):ℝ))) θ := by
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  unfold preferredRightAwayMassIntegrand
  by_cases hd : R/(2*((n+1:ℕ):ℝ))≤preferredAngularDiameter w
  · rw [ite_eq_left hd]
    apply ENNReal.ofReal_le_ofReal
    change ‖(preferredEqualityCutoff R w:ℂ)*_‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (preferredEqualityCutoff_bounds R w).1]
    exact (mul_le_mul_of_nonneg_right (preferredEqualityCutoff_bounds R w).2
      (norm_nonneg _)).trans_eq (one_mul _)
  · rw [ite_eq_right hd]
    have hz := preferredEqualityCutoff_zero_of_small_diameter (by omega : 0<n+1) hR w (le_of_not_ge hd)
    change ENNReal.ofReal ‖(preferredEqualityCutoff R w:ℂ)*_‖≤0
    rw [hz,Complex.ofReal_zero,zero_mul,norm_zero,ENNReal.ofReal_zero]

/-- All transported punctured integrals have the logarithmic bound at every
even N>=2. No relation between N and the derivative order is assumed. -/
theorem preferred_actual_punctured_right_mass (d : PreferredBranchData) :
    ∃cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀B : PreferredCoareaBump d,B.delta<cap→
    ∃δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
    ∀δB : ℝ,0<δB→δB≤δ₀→∀τ : ℝ,0≤τ→τ<τ₀→
    ∀rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut→
    ∀n : ℕ,2≤n+1→Even (n+1)→∀j : ℕ,∀R : ℝ,0<R→
    ∃A : ℝ,0<A ∧ ∀ε : ℝ,0<ε→ε<ε₀→
      ‖preferredPuncturedRightIntegral n d B τ rcut j R ε‖≤A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hs⟩ := preferred_actual_right_away_equality_mass d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,hb⟩ := hs B hB
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,?_⟩
  intro δB hδB hδB₀ τ hτ hτr rcut hcut n hN hEven j R hR
  obtain ⟨A,hA,hbound⟩ := hb δB hδB hδB₀ τ hτ hτr rcut hcut n hN hEven j
    (R/(2*((n+1:ℕ):ℝ))) (by positivity)
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  have hdom := (lintegral_mono (μ:=volume.restrict (angularBox n))
    (preferredPuncturedDensity_away_domination d B τ rcut j ε hR)).trans (hbound ε hε hεr)
  apply (norm_integral_le_lintegral_norm _).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end
end IsingBulk.Preferred22
