import IsingBulk.Preferred22.LowerRightDerivativeLog
import IsingBulk.Preferred22.ActualAnchorBound
import IsingBulk.Preferred22.SelectedKernelDisk
import IsingBulk.Preferred22.FiniteLogAssembly

/-! Actual lower positive-even coefficients, including two: the selected,
anchor and entire right contour are combined before the finite FTC step. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem preferred_actual_lower_coefficient_derivative_log (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ)
    (hN : 2≤n+1) (hEven : Even (n+1)) (hNp : n+1<2*p) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ j : ℕ,∃ C : ℝ,0<C ∧
      ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
          C*(1+|Real.log ε|) := by
  obtain ⟨cR,hcR,_hcRa,hright⟩ := preferred_actual_lower_right_derivative_log d hp hp5 ha hα
  obtain ⟨cA,hcA,_hcAa,hanchor⟩ := preferred_actual_anchor_absolute_bound d
  let cap := min cR cA
  have hcap : 0<cap := lt_min hcR hcA
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨δR,τR,εR,hδR,hδRB,hτR,hεR,hright'⟩ :=
    hright B (hB.trans_le (min_le_left _ _)) n hN hEven hNp
  let δB := min δR (preferredRightMargin d B)/2
  have hmargin := preferredRightMargin_bounds d B
  have hδB : 0<δB := half_pos (lt_min hδR hmargin.1)
  have hδBR : δB≤δR := by dsimp only [δB]; linarith [min_le_left δR (preferredRightMargin d B)]
  have hδBm : δB≤preferredRightMargin d B := by
    dsimp only [δB]
    linarith [min_le_right δR (preferredRightMargin d B)]
  let rcut := preferredRightCutoff d δB
  have hcut : PreferredRightCutoffData d B δB rcut := preferred_right_cutoff_data_of_le d B hδB hδBm
  obtain ⟨εA,τA,hεA,_hεA1,hτA,hanchor'⟩ :=
    hanchor B (hB.trans_le (min_le_right _ _)) δB hδB (hδBR.trans_lt hδRB)
  obtain ⟨ρ,hρ,_hρ1,hselected⟩ := preferred_actual_selected_finite_orders d hcap
  let τ := min τR (min τA ρ)/2
  have hτ : 0<τ := half_pos (lt_min hτR (lt_min hτA hρ))
  have hτR' : τ<τR := by
    dsimp only [τ]
    linarith [min_le_left τR (min τA ρ)]
  have hτA' : τ<τA := by
    have hh := (min_le_right τR (min τA ρ)).trans (min_le_left τA ρ)
    dsimp only [τ]
    linarith
  have hτρ : τ<ρ := by
    have hh := (min_le_right τR (min τA ρ)).trans (min_le_right τA ρ)
    dsimp only [τ]
    linarith
  let ε₀ := min εR (min εA ρ)
  have hε₀ : 0<ε₀ := lt_min hεR (lt_min hεA hρ)
  have hεR' : ε₀≤εR := min_le_left _ _
  have hεA' : ε₀≤εA := (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε₀≤ρ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε₀,hε₀,?_⟩
  intro j
  obtain ⟨CF,hCF,hF⟩ := hselected τ hτ hτρ n hN hEven j
  obtain ⟨CA,J,hCA,hA⟩ := hanchor' τ hτ.le hτA' rcut hcut j j le_rfl
  obtain ⟨CR,hCR,hR⟩ := hright' δB hδB hδBR rcut hcut τ hτ.le hτR' j
  let KA := CA^(n+1)*((n+1:ℕ):ℝ)^(-((n+1:ℕ):ℝ)/2+(J:ℝ))
  have hKA : 0≤KA := by dsimp only [KA]; positivity
  refine ⟨CF+2*(CR+KA),by positivity,?_⟩
  intro ε hε hεr
  have hFb := hF ε hε (hεr.trans_le hερ)
  have hAb := hA n hN hEven ε hε (hεr.trans_le hεA')
  have hRb := hR ε hε (hεr.trans_le hεR')
  rw [preferred_complete_derivative_partition n hEven d B hτ.le rcut
    hcut.2.2.1 hcut.2.2.2.1 j hε]
  let F := iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m)
    (IsingBulk.Branch.radialParameter d.alpha ε)
  let R := iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
    preferredPopulationCutoff B.p B.m rcut 0) (IsingBulk.Branch.radialParameter d.alpha ε)
  let A := fun a : Fin (n+1) => iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
    preferredPopulationCutoff B.p B.m rcut 0) (IsingBulk.Branch.radialParameter d.alpha ε)
  change ‖F+2*(R+∑a,A a)‖≤_
  calc
    _ ≤ ‖F‖+‖(2:ℂ)*(R+∑a,A a)‖ := norm_add_le _ _
    _ = ‖F‖+2*‖R+∑a,A a‖ := by rw [norm_mul]; norm_num
    _ ≤ ‖F‖+2*(‖R‖+∑a,‖A a‖) := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))) (by norm_num))
    _ ≤ CF+2*(CR*(1+|Real.log ε|)+KA) :=
      add_le_add hFb (mul_le_mul_of_nonneg_left (add_le_add hRb hAb) (by norm_num))
    _ ≤ (CF+2*(CR+KA))*(1+|Real.log ε|) := by
      nlinarith [mul_nonneg hCF.le (abs_nonneg (Real.log ε)),
        mul_nonneg hKA (abs_nonneg (Real.log ε))]

/-- The complete finite lower-order complement has bounded kth derivative
norm sum. The next derivative is integrated by the actual radial FTC. -/
theorem preferred_actual_finite_complement (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (k : ℕ) :
    PreferredFiniteComplementStatement (Complex.exp ((d.alpha:ℂ)*Complex.I)) (p-1) k := by
  apply preferred_finite_complement_of_next_log_bounds (Complex.norm_exp_ofReal_mul_I _) (p-1) k
  intro n hn
  have hNeq : 2*n+1+1=2*(n+1) := by omega
  obtain ⟨ε₀,hε₀,hb⟩ := preferred_actual_lower_coefficient_derivative_log d hp hp5 ha hα
    (2*n+1) (by omega) ⟨n+1,by omega⟩ (by omega)
  obtain ⟨C,hC,hCbound⟩ := hb (k+1)
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε hε hεr
  simpa only [hNeq,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hCbound ε hε hεr

end
end IsingBulk.Preferred22
