import IsingBulk.Tail.AllBranchExteriorTruncation
import IsingBulk.Tail.AllBranchExteriorInverseJets
import IsingBulk.Tail.AllBranchExteriorDiagonalNull

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie Set Filter MeasureTheory
open scoped Topology

def allBranchTruncationScale (k : ℕ) : ℝ := Real.exp (-(k:ℝ))

theorem allBranchTruncationScale_pos (k : ℕ) : 0 < allBranchTruncationScale k := Real.exp_pos _

theorem allBranchTruncationScale_tendsto : Tendsto allBranchTruncationScale atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem allBranchExterior_truncation_germ_eventually {N : ℕ} (M : ℕ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) (hu : u p ≠ u q) :
    ∀ᶠ k in atTop, allBranchTruncatedWeight M (allBranchTruncationScale k) p q w =ᶠ[𝓝 u]
      (fun x => w x*allBranchExteriorPairWeight M p q x) := by
  have hδ : 0 < |u p-u q| := abs_pos.mpr (sub_ne_zero.mpr hu)
  have hD : 0 < allBranchExteriorDiameter u := hδ.trans_le (allBranchExterior_pair_le_diameter u p q)
  have hρ : 0 < branchShapeRadius u := by
    have hd := allBranchExterior_diameter_shape_upper u
    linarith
  have hsmall : ∀ᶠ k in atTop,
      allBranchTruncationScale k < min |u p-u q| (branchShapeRadius u)/4 :=
    allBranchTruncationScale_tendsto.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall] with k hk
  let h := allBranchTruncationScale k
  have hh : 0 < h := allBranchTruncationScale_pos k
  have hδu : h < |u p-u q| := by
    have hx := min_le_left |u p-u q| (branchShapeRadius u)
    dsimp [h]
    linarith
  have hρu : 2*h < branchShapeRadius u := by
    have hx := min_le_right |u p-u q| (branchShapeRadius u)
    dsimp [h]
    linarith
  have hcδ : ContinuousAt (fun x : Fin N → ℝ => |x p-x q|) u :=
    (((continuous_apply p).sub (continuous_apply q)).abs).continuousAt
  have hcρ : ContinuousAt (@branchShapeRadius N) u := by unfold branchShapeRadius branchMean; fun_prop
  have hnδ := (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ => h) u).eventually_lt hcδ hδu
  have hnρ := (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ => 2*h) u).eventually_lt hcρ hρu
  filter_upwards [hnδ,hnρ] with x hxδ hxρ
  have hzero : microCutoffBase ((x p-x q)/h)=0 := by
    by_contra hn
    have hb := fixedBranchBump_support 1 (by norm_num) hn
    rw [abs_div,abs_of_pos hh] at hb
    have ht := (div_lt_iff₀ hh).mp hb
    linarith
  have hone : branchFarCutoff h x=1 := by
    apply thresholdStep_one (by nlinarith [sq_pos_of_pos hh])
    rw [branchShapeSquare_eq]
    nlinarith
  change allBranchTruncatedWeight M h p q w x=w x*allBranchExteriorPairWeight M p q x
  simp only [allBranchTruncatedWeight,allBranchTruncationGate,allBranchSelectedGuard,hzero,
    sub_zero,mul_one,hone]

theorem allBranchExterior_truncated_jets_eventually {N : ℕ} (M : ℕ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) (hu : u p ≠ u q) :
    ∀ᶠ k in atTop, ∀ l : List (Fin N),
      cutoffJet l (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w) u=
        cutoffJet l (fun x => w x*allBranchExteriorPairWeight M p q x) u := by
  filter_upwards [allBranchExterior_truncation_germ_eventually M p q w u hu] with k hk
  intro l
  exact allBranchExterior_cutoffJet_congr l _ _ u hk

theorem allBranchExterior_truncated_source_sums_eventually {n : ℕ} (M : ℕ) (p q : Fin (n+1))
    (w : AngularSpace n → ℝ) (u : AngularSpace n) (hu : u p ≠ u q)
    (v θ : ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) :
    ∀ᶠ k in atTop, ∀ j : ℕ, ∀ s : ℂ,
      sourceTermSum p q v θ (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w) Q j s u=
        sourceTermSum p q v θ (fun x => w x*allBranchExteriorPairWeight M p q x) Q j s u := by
  filter_upwards [allBranchExterior_truncated_jets_eventually M p q w u hu] with k hk
  intro j s
  unfold sourceTermSum
  congr 1
  apply List.map_congr_left
  intro T _
  rw [T.sourceValue_eq,T.sourceValue_eq]
  simp only [SourceJetTerm.value,hk T.cutoff]

theorem allBranchExterior_truncated_source_sums_ae_tendsto {n : ℕ} (M : ℕ) (p q : Fin (n+1))
    (hpq : p ≠ q) (w : AngularSpace n → ℝ) (v θ : ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) :
    ∀ᵐ u : AngularSpace n, Tendsto
      (fun k => sourceTermSum p q v θ (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w) Q j s u)
      atTop (𝓝 (sourceTermSum p q v θ (fun x => w x*allBranchExteriorPairWeight M p q x) Q j s u)) := by
  filter_upwards [allBranchExterior_ae_selected_distinct p q hpq] with u hu
  have he := (allBranchExterior_truncated_source_sums_eventually M p q w u hu v θ Q).mono
    (fun _ hk => hk j s)
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with k hk
  exact hk.symm

end
end IsingBulk.Tail
