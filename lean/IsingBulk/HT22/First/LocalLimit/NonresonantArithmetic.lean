import IsingBulk.HT22.First.LocalLimit.NonresonantChart
import IsingBulk.HT22.Arithmetic.FullFamily

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex IsingBulk.First IsingBulk.PrimeFamily Arithmetic

/-- The literal exponential resonance recovers an integer angular index. -/
theorem resonance_eq_angle {N : ℕ} (hN : 0<N) {α : ℝ}
    (hα : exp (-(N:ℂ)*(α:ℂ)*I)=1) : ∃ l : ℤ,α=angle N l := by
  obtain ⟨m,hm⟩ := exp_eq_one_iff.mp hα
  have him := congrArg Complex.im hm
  simp at him
  refine ⟨-m,?_⟩
  unfold angle
  push_cast
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  apply (eq_div_iff hNr).mpr
  nlinarith

theorem regular_two_resonances_Nickel (a : RegularChartData) {N : ℕ} (hN : 0<N)
    (ha : exp (-(N:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(N:ℂ)*(a.beta:ℂ)*I)=1) :
    NickelAt (exp ((a.theta:ℂ)*I)) N := by
  obtain ⟨l,hl⟩ := resonance_eq_angle hN ha
  obtain ⟨m,hm⟩ := resonance_eq_angle hN hb
  refine ⟨norm_exp_ofReal_mul_I _,l,m,?_⟩
  rw [exp_angle_add_inv,←hl,←hm]
  have hrel := congrArg (fun x : ℝ => (x:ℂ)) a.angle_relation
  simp only [ofReal_add,ofReal_mul,ofReal_ofNat] at hrel
  exact hrel.symm

/-- The exact lower-order prime exclusion discharges the product-gap
hypothesis of nonresonant equality-chart analyticity. -/
theorem lower_prime_regular_chart_nonresonant {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {i : ℤ} (hi : PrimeIndex p i) (a : RegularChartData)
    (hθ : a.theta=angle p i) {N : ℕ} (hN : 0<N) (hNp : N<p)
    (ha : exp (-(N:ℂ)*(a.alpha:ℂ)*I)=1) :
    exp (-(N:ℂ)*(a.beta:ℂ)*I)≠1 := by
  intro hb
  have hn := regular_two_resonances_Nickel a hN ha hb
  rw [hθ] at hn
  exact (primeRoot_first_order hp hp5 hi).2.2 N hN hNp hn

/-- At the first order, every equality mean with a different cosine is
regular; the exact prime uniqueness theorem is used rather than assumed. -/
theorem first_prime_other_regular_chart_nonresonant {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {i : ℤ} (hi : PrimeIndex p i) (a : RegularChartData)
    (hθ : a.theta=angle p i) (hother : Real.cos a.alpha≠Real.cos (angle p i))
    (ha : exp (-(p:ℂ)*(a.alpha:ℂ)*I)=1) :
    exp (-(p:ℂ)*(a.beta:ℂ)*I)≠1 := by
  intro hb
  obtain ⟨l,hl⟩ := resonance_eq_angle hp.pos ha
  obtain ⟨m,hm⟩ := resonance_eq_angle hp.pos hb
  have hrel : angleRoot p i+(angleRoot p i)⁻¹ =
      (Real.cos (angle p l):ℂ)+(Real.cos (angle p m):ℂ) := by
    rw [angleRoot,exp_angle_add_inv,←hθ,←hl,←hm]
    exact_mod_cast a.angle_relation.symm
  have h := (primeRoot_unique_cosine_pair hp hp5 hi l m hrel).1
  rw [←hl] at h
  exact hother h

end
end IsingBulk.HT22.LocalLimit
