import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! HT-1.0 odd-particle derivative order and collision-exponent arithmetic.
These identities differ from the LT order N²/2−1 and are not aliases for it. -/
namespace IsingBulk.HT.First

/-- The exact HT derivative order k=(p²−1)/2. -/
def derivativeOrder (p : ℕ) : ℕ := (p^2-1)/2

theorem derivativeOrder_of_odd_witness (m : ℕ) :
    derivativeOrder (2*m+1) = 2*m*(m+1) := by
  have hs : (2*m+1)^2 = 2*(2*m*(m+1))+1 := by ring
  unfold derivativeOrder
  omega

/-- Odd squares give precisely 2k+1, rather than the LT relation 2k+2. -/
theorem odd_square_order {p : ℕ} (hp : Odd p) : p^2 = 2*derivativeOrder p+1 := by
  obtain ⟨m,rfl⟩ := hp
  rw [derivativeOrder_of_odd_witness]
  ring

theorem derivativeOrder_four_dvd {p : ℕ} (hp : Odd p) : 4 ∣ derivativeOrder p := by
  obtain ⟨m,rfl⟩ := hp
  rw [derivativeOrder_of_odd_witness]
  rcases Nat.even_or_odd m with hm | hm
  · obtain ⟨r,rfl⟩ := hm
    refine ⟨r*(2*r+1), ?_⟩
    ring
  · obtain ⟨r,rfl⟩ := hm
    refine ⟨(2*r+1)*(r+1), ?_⟩
    ring

theorem derivativeOrder_pos {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    0 < derivativeOrder p := by
  have h := odd_square_order hp
  nlinarith

/-- The rescaled shape radial density has exponent 2k−1 in HT. -/
theorem odd_shape_radial_exponent {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    (p-1)-1+p*(p-1) = 2*derivativeOrder p-1 := by
  have horder := odd_square_order hp
  have hsub : p-1+1=p := by omega
  have hsub' : (p-1)-1+1=p-1 := by omega
  have hpoly : (p-1)-1+p*(p-1)+2 = p^2 := by nlinarith
  omega

/-- The exact conservative coarea lower bound used for every odd tail order. -/
theorem odd_tail_collision_exponent {p N j : ℕ} (hp : Odd p)
    (hN : p+2 ≤ N) (hj : j ≤ derivativeOrder p) :
    4*p+1 ≤ N^2-2*j-4 := by
  have horder := odd_square_order hp
  have hs : (p+2)^2 ≤ N^2 := Nat.pow_le_pow_left hN 2
  have hp1 : 1 ≤ p := hp.pos
  have hlarge : 4*p+1+2*j+4 ≤ N^2 := by nlinarith
  omega

/-- The phase factor attached to the odd Vandermonde density is -i. -/
theorem odd_particle_phase {p : ℕ} (hp : Odd p) :
    Complex.I ^ (-(p^2 : ℤ)) = -Complex.I := by
  have hdiv := derivativeOrder_four_dvd hp
  obtain ⟨m,hm⟩ := hdiv
  have hs : p^2 = 8*m+1 := by rw [odd_square_order hp,hm]; ring
  have hpow : Complex.I^(p^2) = Complex.I := by
    rw [hs,pow_add,pow_mul]
    norm_num
  simp only [← Nat.cast_pow,zpow_neg,zpow_natCast,hpow,Complex.inv_I]

/-- No sign ambiguity remains in d^k, on either selected boundary half. -/
theorem curvature_power_eq_abs {p : ℕ} (hp : Odd p) (d : ℝ) :
    d^(derivativeOrder p) = |d|^(derivativeOrder p) := by
  obtain ⟨m,hm⟩ := derivativeOrder_four_dvd hp
  have hfour : d^4 = |d|^4 := by
    calc
      d^4 = (d^2)^2 := by ring
      _ = (|d|^2)^2 := by rw [sq_abs]
      _ = |d|^4 := by ring
  rw [hm,pow_mul,pow_mul,hfour]

end IsingBulk.HT.First
