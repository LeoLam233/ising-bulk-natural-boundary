import IsingBulk.First.ShapeSource

/-! Exact arithmetic converting the polar exponents to the manuscript notation. -/
namespace IsingBulk.First

/-- The even-order source index k=N²/2−1 has N²=2(k+1). -/
theorem source_shape_order_identity {n : ℕ} (hn : 1 ≤ n) (he : Even (n+1)) :
    (n+1)^2 = 2*(((n+1)^2/2-1)+1) := by
  have h := source_shape_radial_exponent hn he
  have hpoly : (n+1)^2 = (n+1)*n+(n+1) := by ring
  omega

theorem source_shape_beta_argument {n : ℕ} (hn : 1 ≤ n) (he : Even (n+1)) :
    ((((n+1)^2/2-1 : ℕ) : ℝ) + 1/2) = (((n+1 : ℕ) : ℝ)^2-1)/2 := by
  have h : (((n+1 : ℕ) : ℝ)^2) = 2*((((n+1)^2/2-1 : ℕ) : ℝ)+1) := by
    exact_mod_cast source_shape_order_identity hn he
  linarith

/-- The integer-power phase in the source density is one for every even N. -/
theorem even_particle_phase {N : ℕ} (hN : Even N) :
    Complex.I ^ (-(N^2 : ℤ)) = 1 := by
  obtain ⟨p, rfl⟩ := hN
  have hp : Complex.I ^ ((p+p)^2 : ℕ) = 1 := by
    rw [show (p+p)^2 = 4*(p^2) by ring, pow_mul, Complex.I_pow_four, one_pow]
  simp only [← Nat.cast_pow, zpow_neg, zpow_natCast, hp, inv_one]

end IsingBulk.First
