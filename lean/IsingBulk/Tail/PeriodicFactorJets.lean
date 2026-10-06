import IsingBulk.Tail.AnchoredCutoffJets
import IsingBulk.Tail.SelectorJacobianBounds

/-! A finite family of fixed periodic smooth one-variable factors has
uniform C_J^N coordinate-product jets, independently of particle number. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped BigOperators ContDiff

theorem periodic_scalar_jets_bounded (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, k≤J → ∀ x : ℝ, ‖iteratedDeriv k g x‖ ≤ C := by
  have hper (k : ℕ) : Function.Periodic (iteratedDeriv k g) (2*Real.pi) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hp
    | succ k ih => rw [iteratedDeriv_succ]; exact periodic_derivative ih
  have hbound (k : ℕ) : ∃ C : ℝ, ∀ x : ℝ, ‖iteratedDeriv k g x‖ ≤ C := by
    have hb := (hper k).isBounded_of_continuous Real.two_pi_pos.ne'
      (hg.continuous_iteratedDeriv k (by simp))
    obtain ⟨C,_,hC⟩ := hb.exists_pos_norm_le
    exact ⟨C,fun x => hC _ ⟨x,rfl⟩⟩
  induction J with
  | zero =>
    obtain ⟨C,hC⟩ := hbound 0
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro k hk x
    have he : k=0 := by omega
    exact he ▸ (hC x).trans (le_max_right _ _)
  | succ J ih =>
    obtain ⟨C,hC,hprev⟩ := ih
    obtain ⟨D,hD⟩ := hbound (J+1)
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro k hk x
    by_cases hkJ : k≤J
    · exact (hprev k hkJ x).trans (le_max_left _ _)
    · have he : k=J+1 := by omega
      exact he ▸ (hD x).trans (le_max_right _ _)

theorem finite_periodic_factor_product_jets {I : Type*} [Fintype I]
    (g : I → ℝ → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hp : ∀ i, Function.Periodic (g i) (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ labels : Fin N → I,
      ∀ l : List (Fin N), l.length≤J → ∀ u : Fin N → ℝ,
        ‖cutoffJet l (fun x => ∏ i, g (labels i) (x i)) u‖ ≤ C^N := by
  classical
  choose C hC hbound using fun i => periodic_scalar_jets_bounded (g i) (hg i) (hp i) J
  let D : ℝ := 1+∑ i, C i
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => by linarith [hC i])
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hCD (i : I) : C i≤D := by
    have hh := Finset.single_le_sum (f := C) (s := Finset.univ)
      (fun k _ => show 0≤C k by linarith [hC k]) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro N labels l hl u
  have hd (i : Fin N) (k : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv k (g (labels i))) (iteratedDeriv (k+1) (g (labels i)) x) x := by
    have hh := (hg (labels i)).differentiable_iteratedDeriv k
      (by exact_mod_cast (ENat.natCast_lt_top k)) x
    simpa only [iteratedDeriv_succ] using hh.hasDerivAt
  have he := coordinateProduct_word_jet (fun i : Fin N => fun k => iteratedDeriv k (g (labels i))) hd l u
  simp only [iteratedDeriv_zero] at he
  rw [he,norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, D := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => (hbound (labels i) _ (List.count_le_length.trans hl) _).trans (hCD (labels i)))
    _ = _ := by simp

end
end IsingBulk.Tail
