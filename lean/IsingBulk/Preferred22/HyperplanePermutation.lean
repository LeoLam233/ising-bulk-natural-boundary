import IsingBulk.Preferred22.ConstrainedMeasure
import Mathlib.GroupTheory.Perm.Sign

/-! Genuine measure invariance of the affine constrained hyperplane under
every particle permutation, including changes of the eliminated coordinate. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem lintegral_coordinate_permutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin n → ℝ,f (fun i => x (e i)))=∫⁻ x : Fin n → ℝ,f x := by
  let E := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e).symm
  exact hE.lintegral_comp_emb E.measurableEmbedding f

theorem constrainedAtTotal_free_swap {n : ℕ} (k l : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    constrainedAtTotal c (fun i => x ((Equiv.swap k l) i))=
      fun i => constrainedAtTotal c x ((Equiv.swap k.castSucc l.castSucc) i) := by
  have hs : (∑ i,x ((Equiv.swap k l) i))=∑ i,x i := Equiv.sum_comp (Equiv.swap k l) x
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAtTotal,Fin.snoc_last,hs,
      Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last l).symm]
  · by_cases hjk : j=k
    · subst j
      simp only [Equiv.swap_apply_left,constrainedAtTotal,Fin.snoc_castSucc]
    · by_cases hjl : j=l
      · subst j
        simp only [Equiv.swap_apply_right,constrainedAtTotal,Fin.snoc_castSucc]
      · rw [Equiv.swap_apply_of_ne_of_ne
          (fun h => hjk (Fin.castSucc_inj.mp h)) (fun h => hjl (Fin.castSucc_inj.mp h))]
        simp only [constrainedAtTotal,Fin.snoc_castSucc,
          Equiv.swap_apply_of_ne_of_ne hjk hjl]

theorem constrained_hyperplane_lintegral_free_swap {n : ℕ} (k l : Fin n) (c : ℝ)
    (F : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x
      ((Equiv.swap k.castSucc l.castSucc) i)))=
      ∫⁻ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
  simp_rw [← constrainedAtTotal_free_swap]
  exact lintegral_coordinate_permutation (Equiv.swap k l) (fun x => F (constrainedAtTotal c x))

theorem constrained_hyperplane_lintegral_any_swap {n : ℕ} (k l : Fin (n+1)) (c : ℝ)
    (F : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x ((Equiv.swap k l) i)))=
      ∫⁻ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · refine Fin.lastCases ?_ (fun l => ?_) l
    · simp only [Equiv.swap_self,Equiv.refl_apply]
    · rw [Equiv.swap_comm]
      exact constrained_hyperplane_lintegral_swap l c F
  · refine Fin.lastCases ?_ (fun l => ?_) l
    · exact constrained_hyperplane_lintegral_swap k c F
    · exact constrained_hyperplane_lintegral_free_swap k l c F

/-- Any selected pair of extrema can be made the first and eliminated
coordinates. There is no factorial, multiplicity, or Jacobian adjustment. -/
theorem constrained_hyperplane_lintegral_perm {n : ℕ}
    (e : Equiv.Perm (Fin (n+1))) (c : ℝ) (F : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x (e i)))=
      ∫⁻ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
  have hall : ∀ F : (Fin (n+1) → ℝ) → ℝ≥0∞,
      (∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x (e i)))=
        ∫⁻ x : Fin n → ℝ,F (constrainedAtTotal c x) := by
    induction e using Equiv.Perm.swap_induction_on with
    | one => intro F; rfl
    | swap_mul e k l _ ih =>
      intro F
      calc
        _ = ∫⁻ x : Fin n → ℝ,F (fun i => constrainedAtTotal c x (e i)) :=
          constrained_hyperplane_lintegral_any_swap k l c (fun w => F (fun i => w (e i)))
        _ = _ := ih F
  exact hall F

end
end IsingBulk.Preferred22
