import IsingBulk.Preferred22.DerivativePartition
import IsingBulk.Preferred22.RightMassTail

/-! Exact assembly of the full differentiated coefficient tail from the
three actual contour pieces. The unresolved source bounds stay explicit;
the conclusion concerns the literal all-positive-even coefficient sum. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredRightDerivativeTailTerms (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (r : ℝ → ℝ) (Nstar j : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  if Nstar<2*(m+1) then
    ‖iteratedDeriv j (preferredTransportedIntegral (n := 2*m+1) .right B.delta τ
      preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)‖
  else 0

/-- The remaining full right-part estimate, with actual derivatives of its
literal lifted integral. Its finite intermediate block is included. -/
def PreferredRightDerivativeTailStatement (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (r : ℝ → ℝ) (Nstar k : ℕ) : Prop :=
  ∀ j : ℕ,j≤k → ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
    Summable (preferredRightDerivativeTailTerms d B τ r Nstar j ε) ∧
    (∑' m,preferredRightDerivativeTailTerms d B τ r Nstar j ε m)≤C*(1+|Real.log ε|)

/-- No old tail theorem or assumed full coefficient estimate is used. The
actual population derivative estimate, complete named-anchor bound and full
right derivative bound imply the exact manuscript's absolute even tail. -/
theorem preferred_coefficient_tail_of_component_bounds (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {τ ε₀ : ℝ} (hτ : 0≤τ) (hε₀ : 0<ε₀)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hrp : Function.Periodic r (2*Real.pi))
    (Nstar k : ℕ) (hNstar : 2≤Nstar)
    (hF : PreferredSelectedPopulationBound d B τ ε₀)
    (hA : PreferredAnchorAbsoluteBound d B τ ε₀ r k)
    (hR : PreferredRightDerivativeTailStatement d B τ ε₀ r Nstar k) :
    PreferredAbsoluteTailStatement (Complex.exp ((d.alpha:ℂ)*Complex.I)) Nstar k := by
  intro j hj
  obtain ⟨CF,hCF,hFb⟩ := hF j
  obtain ⟨CA,J,hCA,hAb⟩ := hA j hj
  obtain ⟨D,hD,hRb⟩ := hR j hj
  let EF := fun m : ℕ => CF*shellOrderEnvelope CF (3*j+1) (2*(m+1))
  let EA := fun m : ℕ => shellOrderEnvelope CA J (2*(m+1))
  have hEF : Summable EF := (even_shell_order_envelope_summable hCF.le (3*j+1)).mul_left CF
  have hEA : Summable EA := even_shell_order_envelope_summable hCA.le J
  have hEF0 (m : ℕ) : 0≤EF m := by dsimp [EF,shellOrderEnvelope]; positivity
  have hEA0 (m : ℕ) : 0≤EA m := by dsimp [EA,shellOrderEnvelope]; positivity
  let TF := ∑' m,EF m
  let TA := ∑' m,EA m
  have hTF : 0≤TF := tsum_nonneg hEF0
  have hTA : 0≤TA := tsum_nonneg hEA0
  let C := max 1 (TF+2*(D+TA))
  refine ⟨C,ε₀,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hε₀,?_⟩
  intro ε hε hεr
  obtain ⟨hRS,hRB⟩ := hRb ε hε hεr
  let R := preferredRightDerivativeTailTerms d B τ r Nstar j ε
  let H := 1+|Real.log ε|
  have hH : 1≤H := by dsimp [H]; linarith [abs_nonneg (Real.log ε)]
  have hR0 (m : ℕ) : 0≤R m := by
    dsimp [R,preferredRightDerivativeTailTerms]
    split_ifs <;> positivity
  let E := fun m => EF m+2*(R m+EA m)
  have hE : Summable E := hEF.add ((hRS.add hEA).mul_left 2)
  have hE0 (m : ℕ) : 0≤E m :=
    add_nonneg (hEF0 m) (mul_nonneg (by norm_num) (add_nonneg (hR0 m) (hEA0 m)))
  have hbound (m : ℕ) :
      actualHigherTailTerms (Complex.exp ((d.alpha:ℂ)*Complex.I)) Nstar j ε m≤E m := by
    by_cases hcut : Nstar<2*(m+1)
    · have hNeq : 2*m+1+1=2*(m+1) := by omega
      have hEven : Even (2*m+1+1) := ⟨m+1,by omega⟩
      have hN4 : 4≤2*m+1+1 := by omega
      have hpart := preferred_complete_derivative_partition (2*m+1) hEven d B hτ r hr hrp j hε
      have hFb' := hFb (2*m+1) hN4 hEven ε hε hεr
      have hAb' := hAb (2*m+1) (by omega) hEven ε hε hεr
      have hpath : ((1+ε:ℝ):ℂ)*Complex.exp ((d.alpha:ℂ)*Complex.I)=
          IsingBulk.Branch.radialParameter d.alpha ε := rfl
      simp only [actualHigherTailTerms,ite_eq_left hcut,hpath]
      rw [← hNeq,hpart]
      calc
        _ ≤ ‖iteratedDeriv j
              (preferredFullPopulationIntegral (2*m+1) τ preferredPopulationCutoff B.p B.m)
                (IsingBulk.Branch.radialParameter d.alpha ε)‖+
              2*(‖iteratedDeriv j (preferredTransportedIntegral (n := 2*m+1) .right B.delta τ
                preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)‖+
                ∑ a : Fin (2*m+1+1),‖iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
                  preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)‖) := by
          have ha := norm_add_le
            (iteratedDeriv j (preferredFullPopulationIntegral (2*m+1) τ preferredPopulationCutoff B.p B.m)
              (IsingBulk.Branch.radialParameter d.alpha ε))
            (2*(iteratedDeriv j (preferredTransportedIntegral (n := 2*m+1) .right B.delta τ
              preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)+
              ∑ a : Fin (2*m+1+1),iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
                preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)))
          rw [norm_mul] at ha
          rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at ha
          exact ha.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _)))
            (by norm_num : (0:ℝ)≤2)))
        _ ≤ CF*((2*m+1+1:ℕ):ℝ)^(3*j+1)*(CF/Real.sqrt ((2*m+1+1:ℕ):ℝ))^(2*m+1+1)+
              2*(‖iteratedDeriv j (preferredTransportedIntegral (n := 2*m+1) .right B.delta τ
                preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)‖+
                CA^(2*m+1+1)*((2*m+1+1:ℕ):ℝ)^(-((2*m+1+1:ℕ):ℝ)/2+(J:ℝ))) :=
          add_le_add hFb' (mul_le_mul_of_nonneg_left (add_le_add le_rfl hAb') (by norm_num))
        _ = E m := by
          rw [← shell_order_envelope_eq_rpow CA J (2*m+1+1) (by omega)]
          dsimp [E,EF,EA,R,preferredRightDerivativeTailTerms]
          rw [ite_eq_left hcut]
          simp only [hNeq]
          unfold shellOrderEnvelope
          ring
    · simp only [actualHigherTailTerms,ite_eq_right hcut]
      exact hE0 m
  have hnonneg (m : ℕ) :
      0≤actualHigherTailTerms (Complex.exp ((d.alpha:ℂ)*Complex.I)) Nstar j ε m := by
    unfold actualHigherTailTerms
    split_ifs <;> positivity
  have hsum := hE.of_nonneg_of_le hnonneg hbound
  refine ⟨hsum,?_⟩
  unfold actualHigherTail
  calc
    _ ≤ ∑' m,E m := Summable.tsum_le_tsum hbound hsum hE
    _ = TF+2*((∑' m,R m)+TA) := by
      dsimp only [E,TF,TA]
      rw [hEF.tsum_add ((hRS.add hEA).mul_left 2),
        tsum_mul_left (a := (2:ℝ)) (f := fun m => R m+EA m),hRS.tsum_add hEA]
    _ ≤ TF+2*(D*H+TA) := by linarith only [hRB]
    _ ≤ (TF+2*(D+TA))*H := by
      have hpos : 0≤(H-1)*(TF+2*TA) := mul_nonneg (sub_nonneg.mpr hH)
        (add_nonneg hTF (mul_nonneg (by norm_num : (0:ℝ)≤2) hTA))
      nlinarith only [hpos]
    _ ≤ C*H := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end
end IsingBulk.Preferred22
