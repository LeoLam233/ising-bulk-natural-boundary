import IsingBulk.Preferred22.TransportShellPowers

/-! The distinct finite-particle power count retains the entire squared
Vandermonde. Every exponent below is a real exponent or a displayed quotient;
no natural-number subtraction discards derivative losses. -/
namespace IsingBulk.Preferred22
noncomputable section

/-- Every higher finite particle order leaves more than the two powers
needed by the smooth equality-puncture current at the first singularity. -/
theorem higher_order_collision_degree_four {N Nstar j k : ℕ}
    (hNstar : 2≤Nstar) (hN : Nstar+2≤N) (hj : j≤k)
    (hk : 2*k+2=Nstar^2) :
    4≤(N:ℝ)^2-2*(j:ℝ)-3 := by
  have hn : (Nstar:ℝ)+2≤N := by exact_mod_cast hN
  have hs : (2:ℝ)≤Nstar := by exact_mod_cast hNstar
  have hj' : (j:ℝ)≤k := by exact_mod_cast hj
  have hk' : 2*(k:ℝ)+2=(Nstar:ℝ)^2 := by exact_mod_cast hk
  nlinarith [pow_le_pow_left₀ (by positivity : 0≤(Nstar:ℝ)+2) hn 2]

theorem finite_vandermonde_radius_identity (n j : ℕ) {r : ℝ} (hr : 0<r) :
    (r^((n+2)*(n+1))/r^(2*j))*(r^n/r)=
      r^(((n+2:ℕ):ℝ)^2-2*(j:ℝ)-3) := by
  have he : ((n+2:ℕ):ℝ)^2-2*(j:ℝ)-3=
      (((n+2)*(n+1):ℕ):ℝ)+(n:ℝ)-((2*j:ℕ):ℝ)-1 := by
    push_cast
    ring
  rw [he,Real.rpow_sub hr,Real.rpow_sub hr,Real.rpow_add hr,
    Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_one]
  ring

/-- The true coarea factors add N-3 to the full Vandermonde degree. A
genuine finite-mean gap removes the remaining branch scale uniformly. -/
theorem finite_vandermonde_shell_envelope {A C D g S : ℝ}
    (hA : 0<A) (hC : 0<C) (hD : 0<D) (hg : 0<g) (hS : 0<S)
    (n j : ℕ) {r T H : ℝ} (hr : 0<r) (hT : 0<T) (hH : 0≤H)
    (hgT : g≤T) (hTS : Real.sqrt T≤S) :
    (D*(r^((n+2)*(n+1))/r^(2*j)))*
      (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n) ≤
    (D*A^n*C*((n+2:ℕ):ℝ)*S*(32/Real.sqrt g)^n)*
      r^(((n+2:ℕ):ℝ)^2-2*(j:ℝ)-3)*H := by
  have hsq : Real.sqrt g≤Real.sqrt T := Real.sqrt_le_sqrt hgT
  have hquot : 32*r/Real.sqrt T≤32*r/Real.sqrt g :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hg) hsq
  calc
    _ ≤ (D*(r^((n+2)*(n+1))/r^(2*j)))*
        (A^n*(C*((n+2:ℕ):ℝ)*S/r*H)*(32*r/Real.sqrt g)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul
      · gcongr
      · exact pow_le_pow_left₀ (by positivity) hquot n
      · positivity
      · positivity
    _ = (D*A^n*C*((n+2:ℕ):ℝ)*S*(32/Real.sqrt g)^n)*
        ((r^((n+2)*(n+1))/r^(2*j))*(r^n/r))*H := by
      simp only [div_pow,mul_pow]
      ring
    _ = _ := by rw [finite_vandermonde_radius_identity n j hr]

end
end IsingBulk.Preferred22
