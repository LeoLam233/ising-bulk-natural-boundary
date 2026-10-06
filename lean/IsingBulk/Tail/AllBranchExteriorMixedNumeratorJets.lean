import IsingBulk.Tail.AllBranchExteriorVandermondeJets
import IsingBulk.Tail.AllBranchExteriorNumerator

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Filter
open scoped Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem allBranchExterior_direction_word_jet_bound (d : ι → E) (l : List ι)
    (f : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (directionJet d l f) x‖ ≤
      (l.map (fun i => ‖d i‖)).prod*‖iteratedFDeriv ℂ (k+l.length) f x‖ := by
  induction l generalizing k with
  | nil => simp [directionJet]
  | cons a l ih =>
    have hh := analytic_direction_jet_bound (directionJet d l f) x (d a) k
      (directionJet_analytic d l f x hf)
    apply hh.trans
    have hb := mul_le_mul_of_nonneg_left (ih (k+1)) (norm_nonneg (d a))
    have he : k+1+l.length=k+(l.length+1) := by omega
    rw [he] at hb
    simpa only [List.map_cons,List.prod_cons,List.length_cons,mul_assoc] using hb

theorem allBranchExterior_direction_word_bound (d : ι → E) (l : List ι)
    (f : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) :
    ‖directionJet d l f x‖ ≤
      (l.map (fun i => ‖d i‖)).prod*‖iteratedFDeriv ℂ l.length f x‖ := by
  have hb := allBranchExterior_direction_word_jet_bound d l f x hf 0
  rw [norm_iteratedFDeriv_zero,Nat.zero_add] at hb
  exact hb

theorem allBranchExterior_direction_linear_comp (L : E →L[ℂ] F) (d : ι → E) (l : List ι)
    (f : F → ℂ) (x : E) (hf : AnalyticAt ℂ f (L x)) :
    directionJet d l (f ∘ L) x = directionJet (fun i => L (d i)) l f (L x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have he : directionJet d l (f ∘ L) =ᶠ[𝓝 x]
        (fun y => directionJet (fun i => L (d i)) l f (L y)) := by
      have hnear := hf.eventually_analyticAt
      have hpre := L.continuous.continuousAt.tendsto.eventually hnear
      filter_upwards [hpre] with y hy
      exact ih y hy
    have hh := directionJet_analytic (fun i => L (d i)) l f (L x) hf
    simp only [directionJet]
    rw [he.fderiv_eq]
    have hc := congrArg (fun A : E →L[ℂ] ℂ => A (d a))
      (hh.differentiableAt.hasFDerivAt.comp x L.hasFDerivAt).fderiv
    convert! hc using 1

theorem allBranchExterior_numerator_word_bound {N : ℕ}
    (Q : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ)) (J : ℕ) (C : ℝ)
    (hQ : JetBound Q z J C) (l : List (Option (Fin N))) (hl : l.length ≤ J) :
    ‖numeratorJet l Q z‖ ≤ C := by
  have hd (a : Option (Fin N)) : ‖numeratorDirection a‖ ≤ 1 := by
    cases a with
    | none => exact parameterDirection_norm_le
    | some i => exact spatialDirection_norm_le i
  have hp : (l.map (fun a => ‖numeratorDirection a‖)).prod ≤ 1 := by
    clear hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact (mul_le_mul_of_nonneg_left ih (norm_nonneg _)).trans (by simpa using hd a)
  exact (allBranchExterior_direction_word_bound numeratorDirection l Q z hQ.analytic).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hp).trans (hQ.bound l.length hl))

end
end IsingBulk.Tail
