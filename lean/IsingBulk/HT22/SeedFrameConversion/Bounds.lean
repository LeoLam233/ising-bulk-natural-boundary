import IsingBulk.HT22.SeedFrameConversion.Expansion
import IsingBulk.Preferred22.CoefficientNorm
import IsingBulk.Preferred22.RegularExtensions

/-! Quantitative finite-order cost of changing frames, retaining the scalar
normalization outside every derivative. -/
namespace IsingBulk.HT22.SeedFrameConversion
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem flatMap_length_le {α β : Type*} (L : List α) (f : α → List β) (M : ℕ)
    (h : ∀ u∈L, (f u).length≤M) : (L.flatMap f).length≤L.length*M := by
  induction L with
  | nil => simp
  | cons u L ih =>
    have hu := h u (List.mem_cons_self ..)
    have ht := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem expansion_length_le {N : ℕ} (xs : List (Option (Fin N))) :
    (expansion xs).length≤(N+2)^xs.length := by
  induction xs with
  | nil => simp [expansion]
  | cons a xs ih =>
    exact (flatMap_length_le (expansion xs) (stepTerms a) (N+2)
      (fun u _ => stepTerms_length_le a u)).trans (by
        simpa only [List.length_cons,pow_succ] using Nat.mul_le_mul_right (N+2) ih)

theorem frameJet_bound_of_shared {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (j : ℕ) (B A : ℝ) (hB : 0≤B) (hA : 0≤A) (Z t : ℂ) (θ : Fin N → ℝ)
    (hz : (t,θ)∈Ω)
    (hc : ∀ cs : List Bool, cs.length≤j → ‖coefficient cs t‖≤B)
    (hj : ∀ ys : List (Option (Fin N)), ys.length≤j →
      ‖Z*preferredFrameJet τ p m F ys t θ‖≤A)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖Z*frameJet τ p m F xs t θ‖≤((N:ℝ)+2)^j*(B*A) := by
  rw [frameJet_expansion τ δ p m hp hm Ω hΩ hpoint F hF xs t θ hz]
  have he : Z*((expansion xs).map (fun u => termValue τ p m F u t θ)).sum =
      ((expansion xs).map (fun u => Z*termValue τ p m F u t θ)).sum := by
    generalize expansion xs = L
    induction L with
    | nil => simp
    | cons u L ih => simpa only [List.map_cons,List.sum_cons,mul_add] using congrArg (fun v => Z*termValue τ p m F u t θ+v) ih
  rw [he]
  apply (norm_list_sum_map_bound (expansion xs) _ (B*A) ?_).trans
  · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB hA)
    have hn := (expansion_length_le xs).trans (Nat.pow_le_pow_right (by omega) hxs)
    exact_mod_cast hn
  · intro u hu
    obtain ⟨hcu,hwu⟩ := expansion_orders xs u hu
    have hce := hc u.1 (hcu.trans hxs)
    have hje := hj u.2 (hwu.trans hxs)
    have heq : Z*termValue τ p m F u t θ = coefficient u.1 t*(Z*preferredFrameJet τ p m F u.2 t θ) := by
      unfold termValue
      ring
    rw [heq,norm_mul]
    exact mul_le_mul hce hje (norm_nonneg _) hB

def coefficientWords : ℕ → List (List Bool)
  | 0 => [[]]
  | j+1 => [] :: ((coefficientWords j).map (false::·) ++ (coefficientWords j).map (true::·))

theorem mem_coefficientWords (cs : List Bool) (j : ℕ) (h : cs.length≤j) :
    cs ∈ coefficientWords j := by
  induction j generalizing cs with
  | zero => have : cs=[] := List.length_eq_zero_iff.mp (by omega); subst cs; simp [coefficientWords]
  | succ j ih =>
    cases cs with
    | nil => simp [coefficientWords]
    | cons b cs =>
      have hh := ih cs (by simpa using Nat.le_of_succ_le_succ h)
      cases b <;> simp [coefficientWords,hh]

theorem coefficients_compact_bound (K : Set ℂ) (hK : IsCompact K)
    (hB : ∀ t∈K, AnalyticAt ℂ preferredMovingBranch t) (j : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ cs : List Bool, cs.length≤j → ∀ t∈K, ‖coefficient cs t‖≤C := by
  have hL (L : List (List Bool)) : ∃ C : ℝ, 1≤C ∧ ∀ cs∈L, ∀ t∈K, ‖coefficient cs t‖≤C := by
    induction L with
    | nil => exact ⟨1,le_rfl,by simp⟩
    | cons cs L ih =>
      obtain ⟨A,hA,hbound⟩ := ih
      obtain ⟨B,hBnd⟩ := hK.exists_bound_of_continuousOn
        (fun t ht => (coefficient_analyticAt cs t (hB t ht)).continuousAt.continuousWithinAt)
      refine ⟨max A B,le_trans hA (le_max_left _ _),?_⟩
      intro ds hds t ht
      rcases List.mem_cons.mp hds with rfl | hds
      · exact (hBnd t ht).trans (le_max_right _ _)
      · exact (hbound ds hds t ht).trans (le_max_left _ _)
  obtain ⟨C,hC,hbound⟩ := hL (coefficientWords j)
  exact ⟨C,hC,fun cs hcs => hbound cs (mem_coefficientWords cs j hcs)⟩

end
end IsingBulk.HT22.SeedFrameConversion
