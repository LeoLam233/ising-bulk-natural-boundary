import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! Actual unordered index-pair counts for finite color assignments. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

variable {α : Type*} [LinearOrder α]

def orderedIndexPairs (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter (fun p => p.1 < p.2)

theorem orderedIndexPairs_card (s : Finset α) :
    (orderedIndexPairs s).card = s.card.choose 2 := Finset.card_product_filter_lt

def sameColorPairs {k : ℕ} (s : Finset α) (g : α → Fin k) : Finset (α × α) :=
  (orderedIndexPairs s).filter (fun p => g p.1 = g p.2)

theorem sameColorPairs_card {k : ℕ} (s : Finset α) (g : α → Fin k) :
    (sameColorPairs s g).card = ∑ c : Fin k, ((s.filter (fun i => g i=c)).card).choose 2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => g p.1)
    (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro c _
  have he : (sameColorPairs s g).filter (fun p => g p.1=c) =
      orderedIndexPairs (s.filter (fun i => g i=c)) := by
    ext p
    simp only [sameColorPairs,orderedIndexPairs,Finset.mem_filter,Finset.mem_product]
    aesop
  rw [he]
  exact Finset.card_product_filter_lt

omit [LinearOrder α] in
theorem colorFibers_card_sum {k : ℕ} (s : Finset α) (g : α → Fin k) :
    ∑ c : Fin k, (s.filter (fun i => g i=c)).card = s.card := by
  exact (Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (by simp)).symm

theorem sameColorPairs_real_identity {k : ℕ} (s : Finset α) (g : α → Fin k) :
    ((sameColorPairs s g).card : ℝ) =
      ((∑ c : Fin k, ((s.filter (fun i => g i=c)).card : ℝ)^2)-(s.card : ℝ))/2 := by
  rw [sameColorPairs_card,Nat.cast_sum]
  simp_rw [Nat.cast_choose_two,mul_sub,mul_one,← pow_two]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  congr 2
  exact_mod_cast colorFibers_card_sum s g

theorem sameColorPairs_lower {k : ℕ} (hk : 0 < k) (s : Finset α) (g : α → Fin k) :
    (s.card : ℝ)^2/(k : ℝ)/2-(s.card : ℝ)/2 ≤ ((sameColorPairs s g).card : ℝ) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c : Fin k => ((s.filter (fun i => g i=c)).card : ℝ))
  have hc : (∑ c : Fin k, ((s.filter (fun i => g i=c)).card : ℝ))=(s.card : ℝ) := by
    exact_mod_cast colorFibers_card_sum s g
  rw [hc] at hcs
  simp only [Finset.card_univ,Fintype.card_fin] at hcs
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hd : (s.card : ℝ)^2/(k : ℝ) ≤
      ∑ c : Fin k, ((s.filter (fun i => g i=c)).card : ℝ)^2 := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith
  rw [sameColorPairs_real_identity]
  linarith

theorem twoColorPairs_lower (s : Finset α) (g : α → Fin 2) :
    (s.card : ℝ)^2/4-(s.card : ℝ)/2 ≤ ((sameColorPairs s g).card : ℝ) := by
  have h := sameColorPairs_lower (by norm_num : 0<2) s g
  norm_num [div_div] at h ⊢
  exact h

theorem threeColorPairs_lower (s : Finset α) (g : α → Fin 3) :
    (s.card : ℝ)^2/6-(s.card : ℝ)/2 ≤ ((sameColorPairs s g).card : ℝ) := by
  have h := sameColorPairs_lower (by norm_num : 0<3) s g
  norm_num [div_div] at h ⊢
  exact h

/-- Every unordered pair meeting J injects into J times the ambient index set. -/
theorem incidentIndexPairs_card_le (s J : Finset α) :
    ((orderedIndexPairs s).filter (fun p => p.1∈J ∨ p.2∈J)).card ≤ J.card*s.card := by
  classical
  let f : α × α → α × α := fun p => if p.1∈J then p else (p.2,p.1)
  have hm : Set.MapsTo f
      ((orderedIndexPairs s).filter (fun p => p.1∈J ∨ p.2∈J)) ((J ×ˢ s : Finset (α × α)) : Set (α × α)) := by
    intro p hp
    simp only [Finset.mem_coe,Finset.mem_filter,orderedIndexPairs,Finset.mem_product] at hp ⊢
    dsimp [f]
    split_ifs <;> aesop
  have hi : Set.InjOn f
      ((orderedIndexPairs s).filter (fun p => p.1∈J ∨ p.2∈J)) := by
    rintro ⟨a,b⟩ hp ⟨c,d⟩ hq he
    simp only [Finset.mem_coe,Finset.mem_filter,orderedIndexPairs,Finset.mem_product] at hp hq
    dsimp [f] at he
    split_ifs at he <;> simp_all [Prod.ext_iff]
    all_goals exact False.elim (lt_asymm hp (by aesop))
  have hc := Finset.card_le_card_of_injOn f hm hi
  simpa only [Finset.card_product] using hc

theorem threeColorPairs_cross_upper (s : Finset α) (g : α → Fin 3) :
    (((orderedIndexPairs s).filter (fun p => g p.1 ≠ g p.2)).card : ℝ) ≤
      (s.card : ℝ)^2/3 := by
  have h := Finset.card_filter_add_card_filter_not (s := orderedIndexPairs s)
    (fun p => g p.1=g p.2)
  have hr := congrArg (fun n : ℕ => (n:ℝ)) h
  simp only [Nat.cast_add,orderedIndexPairs_card,Nat.cast_choose_two] at hr
  have hs := threeColorPairs_lower s g
  unfold sameColorPairs at hs
  nlinarith

end
end IsingBulk.Tail
