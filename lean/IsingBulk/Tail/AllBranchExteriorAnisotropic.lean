import IsingBulk.Tail.AllBranchExteriorMixedNumeratorJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

def allBranchPhaseScale {N : ℕ} (R : ℝ) : (ℂ × (Fin N → ℂ)) →L[ℂ] (ℂ × (Fin N → ℂ)) :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
    ((R:ℂ) • ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))

theorem allBranchPhaseScale_apply {N : ℕ} (R : ℝ) (z : ℂ × (Fin N → ℂ)) :
    allBranchPhaseScale R z=(z.1,fun i => (R:ℂ)*z.2 i) := rfl

theorem allBranchPhaseScale_norm {N : ℕ} {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1) :
    ‖@allBranchPhaseScale N R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [allBranchPhaseScale_apply,one_mul,Prod.norm_def]
  apply max_le
  · exact le_max_left _ _
  · have he : (fun i => (R:ℂ)*z.2 i)=(R:ℂ) • z.2 := rfl
    rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR]
    exact (mul_le_of_le_one_left (norm_nonneg _) hR1).trans (le_max_right _ _)

def allBranchScaledDirection {N : ℕ} (R : ℝ) : Option (Fin N) → ℂ × (Fin N → ℂ)
  | none => (1,0)
  | some i => (0,fun j => (R:ℂ)⁻¹*(Pi.single i (1:ℂ) : Fin N → ℂ) j)

theorem allBranchScaledDirection_image {N : ℕ} {R : ℝ} (hR : 0 < R) (a : Option (Fin N)) :
    allBranchPhaseScale R (allBranchScaledDirection R a)=numeratorDirection a := by
  have hn : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  cases a with
  | none =>
    apply Prod.ext
    · rfl
    · funext i; simp [allBranchPhaseScale_apply,allBranchScaledDirection,numeratorDirection]
  | some i =>
    apply Prod.ext
    · rfl
    · funext j
      simp [allBranchPhaseScale_apply,allBranchScaledDirection,numeratorDirection,spatialDirection,hn]

theorem allBranchScaledDirection_norm {N : ℕ} {R : ℝ} (hR : 0 < R) (a : Option (Fin N)) :
    ‖allBranchScaledDirection R a‖ = if a.isSome then R⁻¹ else 1 := by
  cases a with
  | none => simp [allBranchScaledDirection,Prod.norm_def]
  | some i =>
    change ‖((0:ℂ),(R:ℂ)⁻¹ • Pi.single i (1:ℂ))‖ = R⁻¹
    simp [Prod.norm_def,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,Pi.norm_single,hR.le]

theorem allBranchScaledDirection_word_norm {N : ℕ} {R : ℝ} (hR : 0 < R)
    (l : List (Option (Fin N))) :
    (l.map (fun a => ‖allBranchScaledDirection R a‖)).prod=(R⁻¹)^(spatialWord l).length := by
  induction l with
  | nil => simp [spatialWord]
  | cons a l ih =>
    rw [List.map_cons,List.prod_cons,ih]
    cases a <;> simp [allBranchScaledDirection_norm hR,spatialWord,pow_succ,mul_comm]

theorem allBranchExterior_anisotropic_word_bound {N : ℕ} {R : ℝ} (hR : 0 < R)
    (Q : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ))
    (hQ : AnalyticAt ℂ Q (allBranchPhaseScale R z)) (l : List (Option (Fin N))) :
    ‖numeratorJet l Q (allBranchPhaseScale R z)‖ ≤
      (R⁻¹)^(spatialWord l).length*‖iteratedFDeriv ℂ l.length (Q ∘ allBranchPhaseScale R) z‖ := by
  have hc := allBranchExterior_direction_linear_comp (allBranchPhaseScale R)
    (allBranchScaledDirection R) l Q z hQ
  have hd : (fun a : Option (Fin N) => allBranchPhaseScale R (allBranchScaledDirection R a))=
      numeratorDirection := funext (allBranchScaledDirection_image hR)
  rw [hd] at hc
  change ‖directionJet numeratorDirection l Q (allBranchPhaseScale R z)‖ ≤ _
  rw [← hc]
  have hb := allBranchExterior_direction_word_bound (allBranchScaledDirection R) l
    (Q ∘ allBranchPhaseScale R) z
    (AnalyticAt.comp (g := Q) (f := allBranchPhaseScale R) hQ ((allBranchPhaseScale R).analyticAt z))
  simpa only [allBranchScaledDirection_word_norm hR] using hb

end
end IsingBulk.Tail
