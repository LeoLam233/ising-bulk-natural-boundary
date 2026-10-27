import IsingBulk.Preferred22.ShellObligations
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact dependent-coordinate changes on the constrained hyperplane. The
affine map is a reflection plus a shear with absolute determinant one; all
integrals retain genuine product Lebesgue measure. -/
namespace IsingBulk.Preferred22
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal

def constrainedAtTotal {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc x (c-∑ i,x i)

theorem constrainedAtTotal_sum {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    (∑ i,constrainedAtTotal c x i)=c := by
  simp only [constrainedAtTotal,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  ring

def dependentSwap {n : ℕ} (k : Fin n) (c : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  Function.update x k (c-∑ i,x i)

theorem dependentSwap_sum {n : ℕ} (k : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    (∑ i,dependentSwap k c x i)=c-x k := by
  rw [dependentSwap,Finset.sum_update_of_mem (Finset.mem_univ k)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k) x]
  ring

theorem dependentSwap_involutive {n : ℕ} (k : Fin n) (c : ℝ) :
    Function.Involutive (dependentSwap k c) := by
  intro x
  change Function.update (dependentSwap k c x) k (c-∑ i,dependentSwap k c x i)=x
  rw [dependentSwap_sum,sub_sub_cancel,dependentSwap,Function.update_idem,Function.update_eq_self]

theorem dependentSwap_continuous {n : ℕ} (k : Fin n) (c : ℝ) :
    Continuous (dependentSwap k c) := by
  unfold dependentSwap
  fun_prop

def dependentSwapMatrix {n : ℕ} (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (1:Matrix (Fin n) (Fin n) ℝ).updateRow k (fun _ => -1)

theorem dependentSwapMatrix_det {n : ℕ} (k : Fin n) : (dependentSwapMatrix k).det = -1 := by
  have he : (fun _ : Fin n => (-1:ℝ))=
      ∑ j : Fin n,(-1:ℝ) • (1:Matrix (Fin n) (Fin n) ℝ) j := by
    funext i
    simp [Matrix.one_apply]
  rw [dependentSwapMatrix,he,Matrix.det_updateRow_sum,Matrix.det_one]
  norm_num

theorem dependentSwapMatrix_mulVec {n : ℕ} (k : Fin n) (x : Fin n → ℝ) :
    (dependentSwapMatrix k).mulVec x=dependentSwap k 0 x := by
  rw [dependentSwapMatrix,Matrix.updateRow_mulVec,Matrix.one_mulVec]
  simp only [dependentSwap,dotProduct,neg_one_mul,Finset.sum_neg_distrib,zero_sub]

theorem dependentSwap_eq_affine {n : ℕ} (k : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    dependentSwap k c x=(dependentSwapMatrix k).mulVec x+Pi.single k c := by
  rw [dependentSwapMatrix_mulVec]
  funext i
  by_cases hi : i=k
  · subst i
    simp [dependentSwap]
    ring
  · simp [dependentSwap,Function.update_of_ne hi,Pi.single_eq_of_ne hi]

def dependentSwapEquiv {n : ℕ} (k : Fin n) (c : ℝ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := (dependentSwap_involutive k c).toPerm (dependentSwap k c)
  measurable_toFun := (dependentSwap_continuous k c).measurable
  measurable_invFun := (dependentSwap_continuous k c).measurable

theorem dependentSwap_measurePreserving {n : ℕ} (k : Fin n) (c : ℝ) :
    MeasurePreserving (dependentSwap k c) volume volume := by
  have hd : (dependentSwapMatrix k).det≠0 := by rw [dependentSwapMatrix_det]; norm_num
  have hM : MeasurePreserving (Matrix.toLin' (dependentSwapMatrix k)) volume volume := by
    refine ⟨(Matrix.toLin' (dependentSwapMatrix k)).continuous_on_pi.measurable,?_⟩
    simpa only [dependentSwapMatrix_det,inv_neg,inv_one,abs_neg,abs_one,
      ENNReal.ofReal_one,one_smul] using Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have h := (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) (Pi.single k c)).comp hM
  convert h using 1
  funext x
  exact dependentSwap_eq_affine k c x

theorem integral_dependentSwap {n : ℕ} (k : Fin n) (c : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (Fin n → ℝ) → E) :
    (∫ x,f (dependentSwap k c x))=∫ x,f x :=
  (dependentSwap_measurePreserving k c).integral_comp (dependentSwapEquiv k c).measurableEmbedding f

/-- The nonnegative change of variables does not presuppose integrability. -/
theorem lintegral_dependentSwap {n : ℕ} (k : Fin n) (c : ℝ)
    (f : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ x,f (dependentSwap k c x))=∫⁻ x,f x :=
  (dependentSwap_measurePreserving k c).lintegral_comp_emb
    (dependentSwapEquiv k c).measurableEmbedding f

theorem setLIntegral_dependentSwap {n : ℕ} (k : Fin n) (c : ℝ)
    (f : (Fin n → ℝ) → ℝ≥0∞) (s : Set (Fin n → ℝ)) :
    (∫⁻ x in dependentSwap k c ⁻¹' s,f (dependentSwap k c x))=∫⁻ x in s,f x :=
  (dependentSwap_measurePreserving k c).setLIntegral_comp_preimage_emb
    (dependentSwapEquiv k c).measurableEmbedding f s

/-- Literal first-coordinate Tonelli, with the other coordinates outermost. -/
theorem lintegral_fin_cons {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞)
    (hf : AEMeasurable f) :
    (∫⁻ x,f x) = ∫⁻ z : Fin n → ℝ, ∫⁻ m : ℝ,f (Fin.cons m z) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  rw [← he.lintegral_comp_emb e.measurableEmbedding f]
  have hf' : AEMeasurable (fun x : ℝ × (Fin n → ℝ) => f (e x)) volume := by
    apply AEMeasurable.comp_measurable _ he.measurable
    rwa [he.map_eq]
  rw [Measure.volume_eq_prod] at hf' ⊢
  rw [lintegral_prod_symm _ hf']
  simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero]
  rfl

theorem constrainedAtTotal_dependentSwap {n : ℕ} (k : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    constrainedAtTotal c (dependentSwap k c x)=
      fun i => constrainedAtTotal c x ((Equiv.swap k.castSucc (Fin.last n)) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAtTotal,Fin.snoc_last,dependentSwap_sum,sub_sub_cancel,
      Equiv.swap_apply_right,Fin.snoc_castSucc]
  · by_cases hj : j=k
    · subst j
      simp only [Equiv.swap_apply_left,constrainedAtTotal,Fin.snoc_castSucc,Fin.snoc_last,
        dependentSwap,Function.update_self]
    · have hc : j.castSucc≠k.castSucc := fun h => hj (Fin.castSucc_inj.mp h)
      rw [Equiv.swap_apply_of_ne_of_ne hc (Fin.castSucc_ne_last j)]
      simp only [constrainedAtTotal,Fin.snoc_castSucc,dependentSwap,Function.update_of_ne hj]

/-- Any selected particle can become the eliminated coordinate with no
Jacobian multiplier. This is valid for actual measurable shell indicators. -/
theorem constrained_hyperplane_integral_swap {n : ℕ} (k : Fin n) (c : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : (Fin (n+1) → ℝ) → E) :
    (∫ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x ((Equiv.swap k.castSucc (Fin.last n)) i)))=
      ∫ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
  simp_rw [← constrainedAtTotal_dependentSwap]
  exact integral_dependentSwap k c (fun x => F (constrainedAtTotal c x))

theorem constrained_hyperplane_lintegral_swap {n : ℕ} (k : Fin n) (c : ℝ)
    (F : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x
      ((Equiv.swap k.castSucc (Fin.last n)) i)))=
      ∫⁻ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
  simp_rw [← constrainedAtTotal_dependentSwap]
  exact lintegral_dependentSwap k c (fun x => F (constrainedAtTotal c x))

/-- Constrained coarea starts from Tonelli on the actual affine graph. No
finite integral or density majorant is assumed by this identity. -/
theorem constrained_hyperplane_lintegral_cons {n : ℕ} (c : ℝ)
    (F : (Fin (n+2) → ℝ) → ℝ≥0∞)
    (hF : AEMeasurable (fun x : Fin (n+1) → ℝ => F (constrainedAtTotal c x))) :
    (∫⁻ x : Fin (n+1) → ℝ,F (constrainedAtTotal c x))=
      ∫⁻ z : Fin n → ℝ, ∫⁻ m : ℝ,
        F (Fin.snoc (Fin.cons m z) (c-m-∑ i,z i)) := by
  rw [lintegral_fin_cons _ hF]
  simp only [constrainedAtTotal,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  congr 1
  funext z
  congr 1
  funext m
  congr 2
  ring

end
end IsingBulk.Preferred22
