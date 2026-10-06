import IsingBulk.Tail.AllBranchExteriorTruncation
import IsingBulk.Tail.CoordinateDifferenceJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem cutoffJet_linear_sequence {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (g : ℕ → ℝ → ℝ) (hg : ∀ k t, HasDerivAt (g k) (g (k+1) t) t)
    (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (fun x => g 0 (L x)) u=
      (l.map (fun i => L (Pi.single i 1))).prod*g l.length (L u) := by
  induction l generalizing u with
  | nil => simp [cutoffJet]
  | cons i l ih =>
    have he : cutoffJet l (fun x => g 0 (L x))=
        (fun x => (l.map (fun j => L (Pi.single j 1))).prod*g l.length (L x)) := funext ih
    rw [cutoffJet,he]
    have hd := ((hg l.length (L u)).comp_hasFDerivAt u L.hasFDerivAt).const_mul
      (l.map (fun j => L (Pi.single j 1))).prod
    have hd' : HasFDerivAt (fun x => (l.map (fun j => L (Pi.single j 1))).prod*g l.length (L x))
        ((l.map (fun j => L (Pi.single j 1))).prod • g (l.length+1) (L u) • L) u := by
      convert! hd using 1
    dsimp only
    rw [hd'.fderiv]
    simp only [smul_apply,smul_eq_mul,List.length_cons,List.map_cons,List.prod_cons]
    ring

def allBranchSelectedGuardFactor (h : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if k=0 then 1-scaledCutoffFactor h 0 t else -scaledCutoffFactor h k t

theorem allBranchSelectedGuardFactor_hasDerivAt (h : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (allBranchSelectedGuardFactor h k) (allBranchSelectedGuardFactor h (k+1) t) t := by
  by_cases hk : k=0
  · subst k
    convert! (scaledCutoffFactor_hasDerivAt h 0 t).const_sub 1 using 1
  · have hf : allBranchSelectedGuardFactor h k=(fun x => -scaledCutoffFactor h k x) := by
      funext x
      simp only [allBranchSelectedGuardFactor,hk,ite_false]
    rw [hf]
    simp only [allBranchSelectedGuardFactor,show k+1≠0 by omega,ite_false]
    convert! (scaledCutoffFactor_hasDerivAt h k t).neg using 1

theorem allBranchSelectedGuard_word {N : ℕ} (h : ℝ) (p q : Fin N)
    (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (allBranchSelectedGuard h p q) u=
      (l.map (fun i => (if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0))).prod*
        allBranchSelectedGuardFactor h l.length (u p-u q) := by
  have he : allBranchSelectedGuard h p q=(fun x => allBranchSelectedGuardFactor h 0 (coordinateDifference p q x)) := by
    funext x
    simp [allBranchSelectedGuard,allBranchSelectedGuardFactor,scaledCutoffFactor,coordinateDifference]
  rw [he]
  simpa [coordinateDifference,Pi.single_apply,eq_comm] using
    cutoffJet_linear_sequence (coordinateDifference p q) (allBranchSelectedGuardFactor h)
      (allBranchSelectedGuardFactor_hasDerivAt h) l u

theorem allBranchSelectedGuard_range {N : ℕ} (h : ℝ) (p q : Fin N) (u : Fin N → ℝ) :
    0 ≤ allBranchSelectedGuard h p q u ∧ allBranchSelectedGuard h p q u ≤ 1 := by
  have h₁ : 0 ≤ microCutoffBase ((u p-u q)/h) := (fixedBranchBump 1 (by norm_num)).nonneg
  have h₂ : microCutoffBase ((u p-u q)/h) ≤ 1 := (fixedBranchBump 1 (by norm_num)).le_one
  unfold allBranchSelectedGuard microCutoffBase
  constructor <;> linarith

theorem allBranchSelectedGuard_jet_bounds (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ h : ℝ, 0 < h → ∀ p q : Fin N,
      ∀ l : List (Fin N), l.length ≤ J → ∀ u : Fin N → ℝ,
      ‖cutoffJet l (allBranchSelectedGuard h p q) u‖ ≤ C*(h⁻¹)^l.length := by
  obtain ⟨C,hC,hbound⟩ := microCutoffBase_derivatives_bounded J
  refine ⟨C,hC,?_⟩
  intro N h hh p q l hl u
  by_cases hl0 : l=[]
  · subst l
    simp only [cutoffJet,List.length_nil,pow_zero,mul_one]
    rw [Real.norm_eq_abs,abs_of_nonneg (allBranchSelectedGuard_range h p q u).1]
    exact (allBranchSelectedGuard_range h p q u).2.trans hC
  · rw [allBranchSelectedGuard_word,norm_mul]
    have hs (i : Fin N) : ‖(if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0)‖ ≤ 1 := by
      split_ifs <;> norm_num
    have hp : ‖(l.map (fun i => (if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0))).prod‖ ≤ 1 := by
      clear hl hl0
      induction l with
      | nil => simp
      | cons i l ih =>
        rw [List.map_cons,List.prod_cons,norm_mul]
        exact (mul_le_mul (hs i) ih (norm_nonneg _) (by norm_num)).trans (by norm_num)
    have hlen : l.length ≠ 0 := by
      cases l with
      | nil => exact False.elim (hl0 rfl)
      | cons a l => simp
    have hg : ‖allBranchSelectedGuardFactor h l.length (u p-u q)‖ ≤ C*(h⁻¹)^l.length := by
      simp only [allBranchSelectedGuardFactor,hlen,ite_false,norm_neg,scaledCutoffFactor,norm_mul,norm_pow,
        Real.norm_eq_abs,abs_of_pos hh,abs_inv]
      have hb := hbound l.length hl ((u p-u q)/h)
      rw [Real.norm_eq_abs] at hb
      nlinarith [pow_nonneg (inv_nonneg.mpr hh.le) l.length]
    exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans hg

/-- The selected guard costs its actual coordinate separation, uniformly in
its truncation radius. Outside its transition every positive jet is zero. -/
theorem allBranchSelectedGuard_distance_jets (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ h : ℝ, 0 < h → ∀ p q : Fin N,
      ∀ u : Fin N → ℝ, u p ≠ u q → ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (allBranchSelectedGuard h p q) u‖ ≤ C*(|u p-u q|⁻¹)^l.length := by
  obtain ⟨C,hC,hbound⟩ := allBranchSelectedGuard_jet_bounds J
  refine ⟨C,hC,?_⟩
  intro N h hh p q u hu l hl
  have hδ : 0 < |u p-u q| := abs_pos.mpr (sub_ne_zero.mpr hu)
  by_cases hδh : |u p-u q| ≤ h
  · exact (hbound N h hh p q l hl u).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (inv_anti₀ hδ hδh) l.length)
        (zero_le_one.trans hC))
  · by_cases hl0 : l=[]
    · subst l
      simpa only [List.length_nil,pow_zero] using hbound N h hh p q [] (by simp) u
    · have hlen : l.length ≠ 0 := by
        cases l with
        | nil => exact False.elim (hl0 rfl)
        | cons a l => simp
      have hz : iteratedDeriv l.length microCutoffBase ((u p-u q)/h)=0 := by
        by_contra hn
        have hs := microCutoffBase_iterated_support l.length (subset_tsupport _ hn)
        have hb : |(u p-u q)/h| ≤ 1 := abs_le.mpr hs
        rw [abs_div,abs_of_pos hh] at hb
        exact hδh (by have ht := (div_le_iff₀ hh).mp hb; linarith)
      rw [allBranchSelectedGuard_word]
      simp only [allBranchSelectedGuardFactor,hlen,ite_false,scaledCutoffFactor,hz,mul_zero,neg_zero,norm_zero]
      positivity

end
end IsingBulk.Tail
