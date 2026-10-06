import IsingBulk.Tail.AllBranchExteriorScaledJets

/-! Reciprocal coordinate jets from the actual positive denominator gap.
The proof differentiates real functions locally and records every scale power. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Filter
open scoped ContDiff Topology

theorem allBranchExterior_cutoffJet_congr {N : ℕ} (l : List (Fin N))
    (f g : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) (he : f =ᶠ[𝓝 u] g) :
    cutoffJet l f u=cutoffJet l g u := by
  induction l generalizing u with
  | nil => exact he.eq_of_nhds
  | cons i l ih =>
    have hh : cutoffJet l f =ᶠ[𝓝 u] cutoffJet l g := by
      filter_upwards [he.eventually_nhds] with x hx
      exact ih x hx
    exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hh.fderiv_eq

theorem allBranchExterior_cutoffJet_neg {N : ℕ} (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    cutoffJet l (fun x => -f x)=fun x => -cutoffJet l f x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext u
    simp only [cutoffJet,ih,fderiv_fun_neg,neg_apply]

def allBranchExteriorInverseJetConstant (B : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => allBranchExteriorInverseJetConstant B j+
      4^j*(allBranchExteriorInverseJetConstant B j)^2*B

theorem allBranchExteriorInverseJetConstant_one_le (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    1 ≤ allBranchExteriorInverseJetConstant B j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hh : 0 ≤ (4:ℝ)^j*(allBranchExteriorInverseJetConstant B j)^2*B := by positivity
    simp only [allBranchExteriorInverseJetConstant]
    linarith

theorem allBranchExterior_inverse_first {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (u : Fin N → ℝ) (hF : DifferentiableAt ℝ F u) (hne : F u ≠ 0) (i : Fin N) :
    cutoffJet [i] (fun x => (F x)⁻¹) u =
      -((F u)⁻¹*(F u)⁻¹*cutoffJet [i] F u) := by
  have hh := ((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp u hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => (F x)⁻¹) u = _ at hh
  simp only [cutoffJet]
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.mulLeftRight_apply]
  ring

theorem allBranchExterior_scaled_inverse {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hF : ∀ x ∈ U, ContDiffAt ℝ ∞ F x)
    (hne : ∀ x ∈ U, F x ≠ 0) (u : Fin N → ℝ) (hu : u ∈ U)
    (J : ℕ) (d B : ℝ) (hd : 0 < d) (m : ℤ)
    (hJets : AllBranchExteriorScaledJets F u J d B m) (hgap : d^m ≤ F u) :
    AllBranchExteriorScaledJets (fun x => (F x)⁻¹) u J d
      (allBranchExteriorInverseJetConstant B J) (-m) := by
  have hR : ∀ x ∈ U, ContDiffAt ℝ ∞ (fun x => (F x)⁻¹) x := fun x hx => (hF x hx).inv (hne x hx)
  have hFpos : 0 < F u := (zpow_pos hd m).trans_le hgap
  have hbase : ‖(F u)⁻¹‖ ≤ d^(-m) := by
    rw [norm_inv,Real.norm_eq_abs,abs_of_pos hFpos,zpow_neg]
    exact inv_anti₀ (zpow_pos hd m) hgap
  suffices ∀ j ≤ J, AllBranchExteriorScaledJets (fun x => (F x)⁻¹) u j d
      (allBranchExteriorInverseJetConstant B j) (-m) from this J le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by norm_num [allBranchExteriorInverseJetConstant],?_⟩
    intro l hl
    have he : l=[] := List.length_eq_zero_iff.mp (by omega)
    subst l
    simpa only [cutoffJet,allBranchExteriorInverseJetConstant,List.length_nil,Nat.cast_zero,sub_zero,one_mul] using hbase
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    let C := allBranchExteriorInverseJetConstant B j
    have hC : 0 ≤ C := hprev.nonneg
    have hstep : 0 ≤ (4:ℝ)^j*C^2*B := by have hh := hJets.nonneg; positivity
    refine ⟨by dsimp [allBranchExteriorInverseJetConstant,C] at *; positivity,?_⟩
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      have hh := hprev.bound [] (by simp)
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hd.le _)
      change C ≤ C+4^j*C^2*B
      linarith
    | @append_singleton l i _ =>
      have hl' : l.length ≤ j := by simp only [List.length_append,List.length_singleton] at hl; omega
      have hDi : AllBranchExteriorScaledJets (cutoffJet [i] F) u j d B (m-1) := by
        refine ⟨hJets.nonneg,?_⟩
        intro k hk
        rw [← cutoffJet_append_word]
        have hh := hJets.bound (k++[i]) (by simp only [List.length_append,List.length_singleton]; omega)
        have he : m-((k++[i]).length:ℤ)=m-1-(k.length:ℤ) := by simp; ring
        rwa [he] at hh
      have hDsm : ∀ x ∈ U, ContDiffAt ℝ ∞ (cutoffJet [i] F) x :=
        fun x hx => coordinate_cutoffJet_contDiffAt [i] F x (hF x hx)
      have hRR := allBranchExterior_scaled_product (fun x => (F x)⁻¹) (fun x => (F x)⁻¹)
        hU hR hR u hu j d C C hd (-m) (-m) hprev hprev
      have hRRD := allBranchExterior_scaled_product (fun x => (F x)⁻¹*(F x)⁻¹) (cutoffJet [i] F)
        hU (fun x hx => (hR x hx).mul (hR x hx)) hDsm u hu j d (2^j*C*C) B hd
        (-m+-m) (m-1) hRR hDi
      have he : cutoffJet [i] (fun x => (F x)⁻¹) =ᶠ[𝓝 u]
          (fun x => -((F x)⁻¹*(F x)⁻¹*cutoffJet [i] F x)) := by
        filter_upwards [hU.mem_nhds hu] with x hx
        exact allBranchExterior_inverse_first F x ((hF x hx).differentiableAt (by simp)) (hne x hx) i
      rw [cutoffJet_append_word,allBranchExterior_cutoffJet_congr l _ _ u he,
        allBranchExterior_cutoffJet_neg,norm_neg]
      have hh := hRRD.bound l hl'
      have hexp : -m+-m+(m-1)-(l.length:ℤ) = -m-((l++[i]).length:ℤ) := by simp; ring
      have hconst : (2:ℝ)^j*(2^j*C*C)*B=4^j*C^2*B := by
        rw [show (4:ℝ)^j=2^j*2^j by rw [← mul_pow]; norm_num]
        ring
      rw [hexp,hconst] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hd.le _)
      change 4^j*C^2*B ≤ C+4^j*C^2*B
      linarith

end
end IsingBulk.Tail
