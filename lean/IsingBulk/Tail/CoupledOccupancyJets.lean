import IsingBulk.Tail.SelectorJacobianBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual coupled normalized occupancy has dimension-uniform finite angular
jets. No occupancy variable is frozen or replaced by an independent scalar. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators ContDiff

def normalizedAngularOccupancy (N : ℕ) (p : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∑ i, p (θ i))/(N:ℝ)

theorem periodic_iteratedFDeriv {p : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic p T) (j : ℕ) :
    Function.Periodic (iteratedFDeriv ℝ j p) T := by
  intro x
  rw [← iteratedFDeriv_comp_add_right j T x]
  exact congrArg (fun f : ℝ → ℝ => iteratedFDeriv ℝ j f x) (funext hp)

theorem normalizedAngularOccupancy_jet_bound {N j : ℕ} (hN : 0<N) (p : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) {B : ℝ} (hB : 0≤B)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B) (θ : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ j (normalizedAngularOccupancy N p) θ‖≤B := by
  let f : Fin N → (Fin N → ℝ) → ℝ := fun i θ => p (θ i)
  have hsmooth (i : Fin N) : ContDiff ℝ j (f i) :=
    (hp.of_le (by simp)).comp (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff
  have hcoord (i : Fin N) : ‖iteratedFDeriv ℝ j (f i) θ‖≤B := by
    change ‖iteratedFDeriv ℝ j (p ∘ (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) θ‖≤B
    rw [(ContinuousLinearMap.proj i).iteratedFDeriv_comp_right hp θ (by simp)]
    have hproj : ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖≤1 := by
      apply (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).opNorm_le_bound (by norm_num)
      intro x
      simpa using norm_le_pi_norm x i
    apply ((iteratedFDeriv ℝ j p (θ i)).norm_compContinuousLinearMap_le _).trans
    have hprod : (∏ _k : Fin j, ‖(ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)‖)≤1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hproj)
    exact (mul_le_mul_of_nonneg_right (hjet (θ i)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
      (mul_le_of_le_one_right hB hprod)
  have hsum : ContDiff ℝ j (fun x => ∑ i, f i x) := ContDiff.sum (fun i _ => hsmooth i)
  have he : normalizedAngularOccupancy N p = (fun x => (N:ℝ)⁻¹ • (∑ i, f i x)) := by
    funext x
    simp [normalizedAngularOccupancy,f,div_eq_mul_inv,mul_comm]
  rw [he,iteratedFDeriv_const_smul_apply' hsum.contDiffAt,
    iteratedFDeriv_fun_sum_apply (fun i _ => (hsmooth i).contDiffAt),norm_smul]
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh : ‖∑ i, iteratedFDeriv ℝ j (f i) θ‖≤(N:ℝ)*B :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hcoord i))
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq (by field_simp)

theorem periodic_normalized_occupancy_jets (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) (j : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
      ‖iteratedFDeriv ℝ j (normalizedAngularOccupancy N p) θ‖≤B := by
  have hb := (periodic_iteratedFDeriv hper j).isBounded_of_continuous Real.two_pi_pos.ne'
    (hp.continuous_iteratedFDeriv (by simp))
  obtain ⟨B,hB,hbound⟩ := hb.exists_pos_norm_le
  refine ⟨B,hB,?_⟩
  intro N hN θ
  exact normalizedAngularOccupancy_jet_bound hN p hp hB.le
    (fun x => hbound _ ⟨x,rfl⟩) θ


theorem constructed_normalized_occupancy_jets (b η α : ℝ) (j : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
      ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ =>
        occupancy (fun i => (constructedSelector b η α).p (x i))/(N:ℝ)) θ‖≤B := by
  exact periodic_normalized_occupancy_jets (constructedSelector b η α).p
    (periodicUpperP_smooth α) (fun x => (constructedSelector_periodic b η α x).2.1) j


theorem constructed_normalized_occupancy_finite_jets (b η α : ℝ) (k : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ, ∀ j≤k,
      ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ =>
        occupancy (fun i => (constructedSelector b η α).p (x i))/(N:ℝ)) θ‖≤B := by
  choose B hB hb using (constructed_normalized_occupancy_jets b η α)
  let C := ∑ j ∈ Finset.range (k+1), B j
  have hC : 0<C := by
    apply Finset.sum_pos
    · intro j _; exact hB j
    · exact ⟨0,by simp⟩
  refine ⟨C,hC,?_⟩
  intro N hN θ j hj
  exact (hb j N hN θ).trans
    (Finset.single_le_sum (fun l _ => (hB l).le) (Finset.mem_range.mpr (by omega)))

end
end IsingBulk.Tail
