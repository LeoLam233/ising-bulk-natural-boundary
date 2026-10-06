import IsingBulk.Tail.CoordinateProductJets

/-! Real coordinate-word scale bookkeeping for rational partition weights.
All smoothness remains on the actual open real chart. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped ContDiff

structure AllBranchExteriorScaledJets {N : ℕ} (f : (Fin N → ℝ) → ℝ)
    (u : Fin N → ℝ) (J : ℕ) (d C : ℝ) (a : ℤ) : Prop where
  nonneg : 0 ≤ C
  bound : ∀ l : List (Fin N), l.length ≤ J → ‖cutoffJet l f u‖ ≤ C*d^(a-(l.length:ℤ))

theorem allBranchExterior_real_list_norm (L : List ℝ) (B : ℝ)
    (h : ∀ x ∈ L, ‖x‖ ≤ B) : ‖L.sum‖ ≤ (L.length:ℝ)*B := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact (norm_add_le _ _).trans (by linarith)

theorem AllBranchExteriorScaledJets.mono {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    {u : Fin N → ℝ} {J K : ℕ} {d C D : ℝ} {a : ℤ}
    (h : AllBranchExteriorScaledJets f u J d C a) (hd : 0 < d) (hK : K ≤ J) (hCD : C ≤ D) :
    AllBranchExteriorScaledJets f u K d D a := by
  refine ⟨h.nonneg.trans hCD,?_⟩
  intro l hl
  exact (h.bound l (hl.trans hK)).trans (mul_le_mul_of_nonneg_right hCD (zpow_nonneg hd.le _))

theorem allBranchExterior_scaled_product {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x)
    (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) (u : Fin N → ℝ) (hu : u ∈ U)
    (J : ℕ) (d C D : ℝ) (hd : 0 < d) (a b : ℤ)
    (hF : AllBranchExteriorScaledJets f u J d C a)
    (hG : AllBranchExteriorScaledJets g u J d D b) :
    AllBranchExteriorScaledJets (fun x => f x*g x) u J d (2^J*C*D) (a+b) := by
  refine ⟨by have hc := hF.nonneg; have hd' := hG.nonneg; positivity,?_⟩
  intro l hl
  rw [cutoffJet_product_word l f g hU hf hg u hu]
  have hterm : ∀ p ∈ cutoffWordSplits l,
      ‖cutoffJet p.1 f u*cutoffJet p.2 g u‖ ≤ C*D*d^(a+b-(l.length:ℤ)) := by
    intro p hp
    have hlen := cutoffWordSplits_orders l p hp
    have hli : p.1.length ≤ J := by omega
    have hlj : p.2.length ≤ J := by omega
    have he : (a-(p.1.length:ℤ))+(b-(p.2.length:ℤ))=a+b-(l.length:ℤ) := by
      have hh : (p.1.length:ℤ)+(p.2.length:ℤ)=(l.length:ℤ) := by exact_mod_cast hlen
      omega
    rw [norm_mul]
    calc
      _ ≤ (C*d^(a-(p.1.length:ℤ)))*(D*d^(b-(p.2.length:ℤ))) :=
        mul_le_mul (hF.bound p.1 hli) (hG.bound p.2 hlj) (norm_nonneg _)
          (mul_nonneg hF.nonneg (zpow_nonneg hd.le _))
      _ = C*D*(d^(a-(p.1.length:ℤ))*d^(b-(p.2.length:ℤ))) := by ring
      _ = _ := by rw [← zpow_add₀ hd.ne',he]
  have hh := allBranchExterior_real_list_norm
    ((cutoffWordSplits l).map (fun p => cutoffJet p.1 f u*cutoffJet p.2 g u))
    (C*D*d^(a+b-(l.length:ℤ))) (by
      intro y hy
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hy
      exact hterm p hp)
  rw [List.length_map,cutoffWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hh
  apply hh.trans
  have hp : (2:ℝ)^l.length ≤ 2^J := pow_le_pow_right₀ (by norm_num) hl
  have hb : 0 ≤ C*D*d^(a+b-(l.length:ℤ)) :=
    mul_nonneg (mul_nonneg hF.nonneg hG.nonneg) (zpow_nonneg hd.le _)
  nlinarith

end
end IsingBulk.Tail
