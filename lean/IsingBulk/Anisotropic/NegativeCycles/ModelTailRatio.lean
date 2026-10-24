import IsingBulk.Anisotropic.NegativeCycles.ModelTail
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeDominance

 theorem constrainedBetaValue_base_order {N j : ℕ} (hj : alpha N≤j)
    (τ c : ℝ) (hτ : 0<τ) (hc : 0<c) :
    constrainedBetaValue N (alpha N) τ c=
      (j.choose (alpha N):ℝ)*τ^(j-alpha N)*constrainedBetaValue N j τ c := by
  rw [Nat.cast_choose ℝ hj]
  unfold constrainedBetaValue
  rw [Nat.sub_self,Nat.factorial_zero,show alpha N+1-alpha N=1 by omega,pow_one,
    show j+1-alpha N=(j-alpha N)+1 by omega,pow_succ]
  have ha : ((alpha N).factorial:ℝ)≠0 := by positivity
  have hjf : (j.factorial:ℝ)≠0 := by positivity
  have hdf : ((j-alpha N).factorial:ℝ)≠0 := by positivity
  field_simp
  simp

 theorem binomial_tail_geometric {a j : ℕ} (hj : 2*a≤j) {u : ℝ}
    (hu : 0≤u) (hu16 : u≤1/16) :
    (j.choose a:ℝ)*u^(j-a)≤(1/2:ℝ)^j := by
  have hchoose : (j.choose a:ℝ)≤(2:ℝ)^j := by exact_mod_cast Nat.choose_le_two_pow j a
  have hp : u^(j-a)≤(1/4:ℝ)^j := by
    calc
      _ ≤ (1/16:ℝ)^(j-a) := pow_le_pow_left₀ hu hu16 _
      _ = (1/4:ℝ)^(2*(j-a)) := by rw [pow_mul]; norm_num
      _ ≤ (1/4:ℝ)^j := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    _ ≤ (2:ℝ)^j*(1/4:ℝ)^j := mul_le_mul hchoose hp (by positivity) (by positivity)
    _ = _ := by rw [←mul_pow]; norm_num

 theorem model_cutoff_ratio_bound {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0<c.re)
    (b : ContDiffBump (0:ℝ)) :
    ‖∫q : Fin n→ℝ,(1-(shapeSpatialCutoff b q:ℂ))*quadraticModelKernel n j τ c q‖≤
      ((j.choose (alpha (n+1)):ℝ)*(τ/(τ+c.re*b.rIn))^(j-alpha (n+1)))*
        constrainedBetaValue (n+1) j τ c.re := by
  have hh := quadraticModel_cutoff_tail_bound ho hn j hj τ hτ c hc b
  rw [constrainedBetaValue_base_order hj τ c.re hτ hc] at hh
  convert hh using 1
  simp only [div_eq_mul_inv,inv_pow]
  ring

 theorem model_cutoff_geometric_bound {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : 2*alpha (n+1)≤j) (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0<c.re)
    (b : ContDiffBump (0:ℝ)) (hsmall : τ/(τ+c.re*b.rIn)≤1/16) :
    ‖∫q : Fin n→ℝ,(1-(shapeSpatialCutoff b q:ℂ))*quadraticModelKernel n j τ c q‖≤
      (1/2:ℝ)^j*constrainedBetaValue (n+1) j τ c.re := by
  have hb := b.rIn_pos
  apply (model_cutoff_ratio_bound ho hn j (by omega) τ hτ c hc b).trans
  apply mul_le_mul_of_nonneg_right _ (constrainedBetaValue_pos (by omega) j hτ hc).le
  exact binomial_tail_geometric hj (by positivity) hsmall

end IsingBulk.Anisotropic.NegativeCycles
