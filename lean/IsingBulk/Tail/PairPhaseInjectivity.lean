import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic

/-! Genuine injectivity of a fixed-sum two-coordinate phase map on a
convex source cell, obtained from its signed directional derivative. -/
namespace IsingBulk.Tail
noncomputable section
open Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem pair_data_recover {N : ℕ} (x y : Fin N → ℝ) (i j : Fin N) (hij : i≠j)
    (hsum : ∑ k, x k=∑ k, y k)
    (hspect : ∀ k, k≠i → k≠j → x k=y k) :
    y=x+(y i-x i) • (Pi.single i (1:ℝ)-Pi.single j 1) := by
  have hy : y=x+(y i-x i) • Pi.single i (1:ℝ)+(y j-x j) • Pi.single j 1 := by
    funext k
    by_cases hki : k=i
    · subst k; simp [Ne.symm hij]
    · by_cases hkj : k=j
      · subst k; simp [hij]
      · simp [hki,hkj,hspect k hki hkj]
  have hh := congrArg (fun z : Fin N → ℝ => ∑ k, z k) hy
  simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,mul_ite] at hh
  have hdelta : y j-x j= -(y i-x i) := by linarith
  calc
    y = x+(y i-x i) • Pi.single i (1:ℝ)+(y j-x j) • Pi.single j 1 := hy
    _ = _ := by rw [hdelta]; module

theorem fixed_sum_pair_phase_injective {N : ℕ} (S : Set (Fin N → ℝ)) (hS : Convex ℝ S)
    (G : (Fin N → ℝ) → ℝ) (i j : Fin N) (hij : i≠j)
    (hG : ∀ x∈S, DifferentiableAt ℝ G x)
    (hpos : ∀ x∈S, 0 < fderiv ℝ G x (Pi.single i 1-Pi.single j 1))
    {x y : Fin N → ℝ} (hx : x∈S) (hy : y∈S)
    (hsum : ∑ k, x k=∑ k, y k) (hphase : G x=G y)
    (hspect : ∀ k, k≠i → k≠j → x k=y k) : x=y := by
  let v : Fin N → ℝ := Pi.single i 1-Pi.single j 1
  let P : ℝ → (Fin N → ℝ) := fun t => x+(t-x i) • v
  let T : Set ℝ := {t | P t∈S}
  have hT : Convex ℝ T := by
    intro a ha b hb c e hc he hce
    have hh := hS ha hb hc he hce
    change P (c*a+e*b)∈S
    convert hh using 1
    have heq : e=1-c := by linarith
    rw [heq]
    funext k
    dsimp [P]
    ring
  have hd (t : ℝ) (ht : t∈T) :
      HasDerivAt (fun z => G (P z)) (fderiv ℝ G (P t) v) t := by
    have hp : HasDerivAt P v t := by
      simpa only [P,id_eq,one_smul] using (((hasDerivAt_id t).sub_const (x i)).smul_const v).const_add x
    exact (hG (P t) ht).hasFDerivAt.comp_hasDerivAt t hp
  have hm : StrictMonoOn (fun t => G (P t)) T := by
    apply strictMonoOn_of_deriv_pos hT
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      have htT : t∈T := interior_subset ht
      exact hpos (P t) htT
  have hxP : P (x i)=x := by simp [P]
  have hyP : P (y i)=y := (pair_data_recover x y i j hij hsum hspect).symm
  have hxi : x i∈T := by change P (x i)∈S; rw [hxP]; exact hx
  have hyi : y i∈T := by change P (y i)∈S; rw [hyP]; exact hy
  have he : x i=y i := hm.injOn hxi hyi (by rw [hxP,hyP]; exact hphase)
  rw [← hyP,← he,hxP]

end
end IsingBulk.Tail
