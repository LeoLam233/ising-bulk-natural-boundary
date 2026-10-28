import IsingBulk.HT22.Arithmetic.PrimeRoot

/-! The same exact equal-angle family is dense in both upper quadrants. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open IsingBulk.PrimeFamily

def primeRootFamily : Set ℂ :=
  {z | ∃ p : ℕ, ∃ a : ℤ, p.Prime ∧ 5≤p ∧ PrimeIndex p a ∧ z=angleRoot p a}

theorem angle_double_index (p : ℕ) (a : ℤ) : angle p (2*a)=2*angle p a := by
  unfold angle
  push_cast
  ring

/-- Double the first-quadrant grid, not the particle order. -/
theorem primeIndex_double_of_admissible {p : ℕ} (hp : 0<p) {a : ℤ}
    (ha : Admissible p a) : PrimeIndex p (2*a) := by
  have ha0 := (admissible_integer_bounds hp ha).1
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hh := (div_lt_iff₀ hpR).mp ha.2
  change 2*Real.pi*(a:ℝ)<Real.pi/2*(p:ℝ) at hh
  have ha4R : 4*(a:ℝ)<p := by nlinarith [Real.pi_pos]
  have ha4 : 4*a<(p:ℤ) := by exact_mod_cast ha4R
  constructor <;> omega

theorem primeRoot_family_dense_upper_arc {t : ℝ} (ht : 0<t) (htπ : t<Real.pi) :
    Complex.exp ((t:ℂ)*Complex.I) ∈ closure primeRootFamily := by
  let f : ℝ → ℂ := fun u => Complex.exp ((u:ℂ)*Complex.I)
  have hf : Continuous f := Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul_const Complex.I)
  change f t ∈ closure primeRootFamily
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨p,a,b,hp,hp11,_hab,ha,_hb,hea,_heb⟩ :=
    neighboring_prime_angles (by linarith : 0<t/2) (by linarith : t/2<Real.pi/2)
      (by linarith : 0<δ/2)
  refine ⟨angleRoot p (2*a),⟨p,2*a,hp,by omega,primeIndex_double_of_admissible hp.pos ha,rfl⟩,?_⟩
  rw [dist_comm]
  apply hcont
  rw [Real.dist_eq,angle_double_index]
  rw [abs_lt] at hea ⊢
  constructor <;> linarith

theorem primeRoot_level_ne_zero {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) : 2*Real.cos (angle p a)≠0 := by
  intro hzero
  apply primeRoot_trace_not_rational hp hp5 ha 0
  have h := exp_angle_add_inv (angle p a)
  change angleRoot p a+(angleRoot p a)⁻¹=_ at h
  rw [h]
  have hC := congrArg (fun x : ℝ => (x:ℂ)) hzero
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_zero,Rat.cast_zero] using hC

/-- The exact parity used by the equal-angle radial period: k ≡ 0 mod 4. -/
theorem prime_critical_order_mod_four {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    ((p^2-1)/2)%4=0 := by
  have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hpmod : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by omega
  have hsq : p^2%8=1 := by
    rcases hpmod with h | h | h | h <;> norm_num [Nat.pow_mod,h]
  omega

end
end IsingBulk.HT22.Arithmetic
