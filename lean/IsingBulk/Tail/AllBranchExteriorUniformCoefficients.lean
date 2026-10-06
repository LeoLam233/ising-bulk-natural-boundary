import Mathlib.Data.Finset.Lattice.Fold
import IsingBulk.Tail.AllBranchExteriorCoefficientBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

theorem allBranchExterior_original_coefficients_finite (d : LocalBranchData) (J k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ j ≤ J,
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N → ∀ p q : Fin N, p ≠ q →
        (sourceJetTerms p q j).length ≤ C*N^C ∧
        ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) → ∀ T ∈ sourceJetTerms p q j,
          JetBound T.regularPart (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) k
            ((C:ℝ)*(N:ℝ)^C) := by
  have hh := fun j : Fin (J+1) => allBranchExterior_original_coefficients d j.val k
  choose C hC r hr h using hh
  let Cstar : ℕ := ∑ j, C j
  let rstar : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  have hCle (j : Fin (J+1)) : C j ≤ Cstar :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hrle (j : Fin (J+1)) : rstar ≤ r j := Finset.inf'_le _ (Finset.mem_univ j)
  have hrpos : 0 < rstar := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hr j)
  refine ⟨Cstar,(hC 0).trans_le (hCle 0),rstar,hrpos,?_⟩
  intro j hj ε hε hεr N hN p q hpq
  let jj : Fin (J+1) := ⟨j,by omega⟩
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hcount,hreg⟩ := h jj ε hε (hεr.trans (hrle jj)) N hN p q hpq
  refine ⟨hcount.trans ?_,?_⟩
  · exact Nat.mul_le_mul (hCle jj) (Nat.pow_le_pow_right hN (hCle jj))
  · intro u hu T hT
    apply (hreg u (fun i => (hu i).trans (hrle jj)) T hT).mono le_rfl
    exact mul_le_mul (by exact_mod_cast hCle jj) (pow_le_pow_right₀ hn (hCle jj))
      (by positivity) (by positivity)

end
end IsingBulk.Tail
