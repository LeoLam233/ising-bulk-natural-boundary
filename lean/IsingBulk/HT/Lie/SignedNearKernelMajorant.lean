import IsingBulk.Tail.AllBranchExteriorNearKernelMajorant
import IsingBulk.HT.Contour.SignedPositiveAttachment
import IsingBulk.HT.Tail.SignedExteriorNegativeTheorem
import IsingBulk.Tail.AllBranchExteriorPositiveAttachment
import IsingBulk.Tail.AllBranchExteriorNegativeTheorem

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Tail IsingBulk.Branch IsingBulk.Lie Set MeasureTheory

def signedExteriorNearKernelMajorant {N : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε R a D : ℝ) (v : Fin N) (Q : ℕ) (u : Fin N → ℝ) : ℝ :=
  (allBranchExteriorPositiveDiameterRegion R a D).indicator
    (fun x => allBranchExteriorDiameter x^Q*signedExteriorKernelDensity σ d ε x) u+
  D^Q*(allBranchExteriorNegativeRegion v R a).indicator (signedExteriorKernelDensity σ d ε) u

theorem signed_near_kernel_majorant_nonneg {N : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε R a D : ℝ) (hD : 0 ≤ D) (v : Fin N) (Q : ℕ) (u : Fin N → ℝ) :
    0 ≤ signedExteriorNearKernelMajorant σ d ε R a D v Q u := by
  apply add_nonneg
  · exact indicator_nonneg (fun x _ => mul_nonneg (pow_nonneg (allBranchExterior_diameter_nonneg x) Q)
      (signed_kernel_density_nonneg σ d ε x)) u
  · exact mul_nonneg (pow_nonneg hD Q)
      (indicator_nonneg (fun x _ => signed_kernel_density_nonneg σ d ε x) u)

theorem signed_near_kernel_majorant_dominates {N : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε R a D : ℝ) (ha : 0 < a) (v : Fin N) (Q : ℕ) (u : Fin N → ℝ)
    (hu : ∀ i, |u i| ≤ R) (hdiam : 0 < allBranchExteriorDiameter u)
    (hD : allBranchExteriorDiameter u ≤ D)
    (hsign : (∀ i, a ≤ u i) ∨ (∀ i, u i ≤ -a)) :
    allBranchExteriorDiameter u^Q*signedExteriorKernelDensity σ d ε u ≤
      signedExteriorNearKernelMajorant σ d ε R a D v Q u := by
  classical
  unfold signedExteriorNearKernelMajorant
  have hn : 0 ≤ (allBranchExteriorNegativeRegion v R a).indicator (signedExteriorKernelDensity σ d ε) u :=
    indicator_nonneg (fun x _ => signed_kernel_density_nonneg σ d ε x) u
  have hp : 0 ≤ (allBranchExteriorPositiveDiameterRegion R a D).indicator
      (fun x => allBranchExteriorDiameter x^Q*signedExteriorKernelDensity σ d ε x) u :=
    indicator_nonneg (fun x _ => mul_nonneg (pow_nonneg (allBranchExterior_diameter_nonneg x) Q)
      (signed_kernel_density_nonneg σ d ε x)) u
  rcases hsign with hpos | hneg
  · have hm : u ∈ allBranchExteriorPositiveDiameterRegion R a D :=
      ⟨⟨fun i => ha.le.trans (hpos i),fun i => (abs_le.mp (hu i)).2⟩,hdiam,hD,v,hpos v⟩
    rw [indicator_of_mem hm]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (hdiam.le.trans hD) Q) hn)
  · have hm : u ∈ allBranchExteriorNegativeRegion v R a := by
      refine ⟨⟨fun i => (abs_le.mp (hu i)).1,fun i => (abs_le.mp (hu i)).2⟩,?_,v,?_⟩
      · rw [abs_of_nonpos (by linarith [hneg v])]
        linarith [hneg v]
      · linarith [hneg v]
    rw [indicator_of_mem hm]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdiam.le hD Q)
      (signed_kernel_density_nonneg σ d ε u)).trans (le_add_of_nonneg_left hp)

theorem signed_near_kernel_majorant_integral (α : ℝ) {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ ζ c C r : ℝ, 0 < ζ ∧ 0 < c ∧ 0 < C ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, ∀ v q : Fin (n+1), v ≠ q →
      ∀ R a D : ℝ, 0 ≤ R → R ≤ r → 0 < a → 0 < D →
      B.original.separationThreshold*ε ≤ a → 2*B.original.C₀*ε ≤ a → ∀ Q : ℕ, 1 ≤ Q →
      Integrable (signedExteriorNearKernelMajorant (Complex.exp (Complex.I*(α:ℂ))) d ε R a D v Q) ∧
      (∫ u, signedExteriorNearKernelMajorant (Complex.exp (Complex.I*(α:ℂ))) d ε R a D v Q u) ≤
        allBranchExteriorNearKernelCost B ε R a D ζ c C (n+1) Q := by
  classical
  obtain ⟨ζ,rP,hζ,hrP,hpositive⟩ := signed_allBranchExterior_positive_weighted_density_integral B hcsmall
  obtain ⟨c,C,rN,hc,hC,hrN,hnegative⟩ := signed_allBranchExterior_negative_kernel_integral α B
  refine ⟨ζ,c,C,min rP rN,hζ,hc,hC,lt_min hrP hrN,?_⟩
  intro ε hε hεr n v q hvq R a D hR hRr ha hD hsmall₁ hsmall₂ Q hQ
  obtain ⟨P,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
  have hpos := hpositive ε hε (hεr.trans (min_le_left _ _)) α n R a D hR
    (hRr.trans (min_le_left _ _)) ha hD hsmall₁ hsmall₂ P
  have hneg := hnegative ε hε (hεr.trans (min_le_right _ _)) n v q hvq R a hR
    (hRr.trans (min_le_right _ _)) ha
  have hSP := @allBranchExterior_positive_diameter_region_measurable (n+1) R a D
  have hSN : MeasurableSet (allBranchExteriorNegativeRegion v R a) := by
    unfold allBranchExteriorNegativeRegion
    measurability
  have hiP := hpos.1.integrable_indicator hSP
  have hiN := hneg.1.integrable_indicator hSN
  refine ⟨hiP.add (hiN.const_mul (D^(P+1))),?_⟩
  unfold signedExteriorNearKernelMajorant
  rw [integral_add hiP (hiN.const_mul _),integral_const_mul,integral_indicator hSP,integral_indicator hSN]
  simpa only [allBranchExteriorNearKernelCost,Nat.cast_add,Nat.cast_one] using
    add_le_add hpos.2 (mul_le_mul_of_nonneg_left hneg.2 (pow_nonneg hD.le (P+1)))

end
end IsingBulk.HT.Lie
