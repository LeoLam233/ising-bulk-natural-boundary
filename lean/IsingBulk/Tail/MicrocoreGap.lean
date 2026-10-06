import IsingBulk.Analysis.BranchData
import IsingBulk.Algebra.Resultant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A nonresonant gap for the actual all-branch microcore product. The
uniform intermediate-window estimates needed to instantiate its smallness
condition remain a separate obligation. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
open Complex

theorem norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i)-(∏ i ∈ s, g i)‖ ≤ ∑ i ∈ s, ‖f i-g i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hp : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) hg'
    have he : f a*(∏ i ∈ s, f i)-g a*(∏ i ∈ s, g i) =
      f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))+(f a-g a)*(∏ i ∈ s, g i) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    have h₁ := mul_le_of_le_one_left (norm_nonneg ((∏ i ∈ s, f i)-(∏ i ∈ s, g i)))
      (hf a (Finset.mem_insert_self _ _))
    have h₂ := mul_le_of_le_one_right (norm_nonneg (f a-g a)) hp
    linarith [ih hf' hg']

def microcoreY (c ε b u : ℝ) : ℂ :=
  Complex.exp ((-c*ε:ℝ)+((-b+u:ℝ):ℂ)*Complex.I)

theorem microcoreY_norm (c ε b u : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    ‖microcoreY c ε b u‖ ≤ 1 := by
  rw [microcoreY, Complex.norm_exp]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  rw [Real.exp_le_one_iff]
  nlinarith

theorem microcoreY_near_center (c ε b u : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    ‖microcoreY c ε b u-Complex.exp (-(b:ℂ)*Complex.I)‖ ≤ c*ε+|u| := by
  let ξ := Complex.exp (-(b:ℂ)*Complex.I)
  let r : ℂ := Complex.exp ((-c*ε:ℝ):ℂ)
  let v := Complex.exp ((u:ℂ)*Complex.I)
  have hξ : ‖ξ‖ = 1 := by dsimp [ξ]; rw [show -(b:ℂ)=((-b:ℝ):ℂ) by simp]; exact Complex.norm_exp_ofReal_mul_I _
  have hv : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he : microcoreY c ε b u = r*ξ*v := by
    dsimp [microcoreY,r,ξ,v]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hr : ‖r-1‖ ≤ c*ε := by
    dsimp [r]
    rw [← Complex.ofReal_exp]
    rw [show (Real.exp (-c*ε):ℂ)-1 = ((Real.exp (-c*ε)-1:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs]
    have hle : Real.exp (-c*ε) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith [Real.add_one_le_exp (-c*ε)]
  have hu : ‖v-1‖ ≤ |u| := by
    simpa [v,mul_comm,Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := u)
  rw [he]
  change ‖r*ξ*v-ξ‖ ≤ _
  rw [show r*ξ*v-ξ=(r-1)*ξ*v+ξ*(v-1) by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,hξ,hv,mul_one,one_mul]
  linarith

/-- The product perturbation is linear in N, with no exponential-in-N
inflation, because all original contour factors have norm at most one. -/
theorem microcore_product_near_center (N : ℕ) (u : Fin N → ℝ)
    (c ε b radius : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hu : ∀ i, |u i| ≤ radius) :
    ‖(∏ i, microcoreY c ε b (u i))-Complex.exp (-(b:ℂ)*Complex.I)^N‖ ≤
      N*(c*ε+radius) := by
  have hn : ‖Complex.exp (-(b:ℂ)*Complex.I)‖ = 1 := by
    rw [show -(b:ℂ)=((-b:ℝ):ℂ) by simp]
    exact Complex.norm_exp_ofReal_mul_I _
  have hp := norm_prod_sub_prod_le Finset.univ (fun i => microcoreY c ε b (u i))
    (fun _ : Fin N => Complex.exp (-(b:ℂ)*Complex.I))
    (fun _ _ => microcoreY_norm _ _ _ _ hc hε) (fun _ _ => hn.le)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
  apply hp.trans
  calc
    _ ≤ ∑ _i : Fin N, (c*ε+radius) := Finset.sum_le_sum (fun i _ =>
      (microcoreY_near_center c ε b (u i) hc hε).trans (by linarith [hu i]))
    _ = _ := by simp; ring

/-- The source exponential gap persists on every sufficiently small actual
microcore, with a single resultant exponent for every positive N. -/
theorem algebraic_microcore_gap (b : ℝ)
    (halg : IsAlgebraic ℚ (Complex.exp (-(b:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(b:ℂ)*Complex.I)^N ≠ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : Fin N → ℝ,
      ∀ c ε radius : ℝ, 0 ≤ c → 0 ≤ ε →
      (∀ i, |u i| ≤ radius) →
      (N:ℝ)*(c*ε+radius) ≤ Real.exp (-A*N)/2 →
      Real.exp (-A*N)/2 ≤ ‖1-∏ i, microcoreY c ε b (u i)‖ := by
  obtain ⟨A,hA,hgap⟩ := IsingBulk.Separation.exponential_separation halg hnot
  refine ⟨A,hA,?_⟩
  intro N hN u c ε radius hc hε hu hsmall
  have hp := microcore_product_near_center N u c ε b radius hc hε hu
  have hg := hgap N hN
  have he : 1-Complex.exp (-(b:ℂ)*Complex.I)^N =
      (1-∏ i, microcoreY c ε b (u i))+
        ((∏ i, microcoreY c ε b (u i))-Complex.exp (-(b:ℂ)*Complex.I)^N) := by ring
  have ht := norm_add_le (1-∏ i, microcoreY c ε b (u i))
    ((∏ i, microcoreY c ε b (u i))-Complex.exp (-(b:ℂ)*Complex.I)^N)
  rw [← he] at ht
  linarith

end
end IsingBulk.Tail
