import IsingBulk.Anisotropic.Geometry.EndpointArithmetic

namespace IsingBulk.Anisotropic
noncomputable section

/-- The first numerator on the forbidden-side odd grid is primitive. -/
theorem forbidden_half_coprime {n : ℕ} (hn : Odd n) :
    Nat.Coprime n ((n-1)/2) := by
  rcases hn with ⟨k,rfl⟩
  have hh : (2*k+1-1)/2=k := by omega
  rw [hh]
  have h := (Nat.coprime_add_mul_right_right k 1 2).mpr (Nat.coprime_one_right k)
  convert h.symm using 1; omega

/-- Primitive rational cosine coordinates force divisibility of the grid order. -/
theorem coprime_dvd_of_grid_cos_eq {p k n : ℕ} (hp : 0<p)
    (hc : Nat.Coprime p k) (hn : 0<n) (j : ℤ)
    (hj : Real.cos (2*Real.pi*j/n)=Real.cos (2*Real.pi*k/p)) : p∣n := by
  obtain ⟨m,hm⟩ := Real.cos_eq_cos_iff.mp hj
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hπ : (2*Real.pi:ℝ)≠0 := by positivity
  have hdiv : (p:ℤ)∣(n:ℤ)*(k:ℤ) := by
    rcases hm with hm | hm
    · have he : (n:ℝ)*k=(p:ℝ)*(m*n+j) := by
        apply mul_left_cancel₀ hπ
        calc
          _ = (2*Real.pi*k/p)*((p:ℝ)*n) := by field_simp
          _ = (2*m*Real.pi+2*Real.pi*j/n)*((p:ℝ)*n) := congrArg (fun x : ℝ => x*((p:ℝ)*n)) hm
          _ = _ := by field_simp
      have hei : (n:ℤ)*(k:ℤ)=(p:ℤ)*(m*(n:ℤ)+j) := by exact_mod_cast he
      exact ⟨m*(n:ℤ)+j,hei⟩
    · have he : (n:ℝ)*k=(p:ℝ)*(m*n-j) := by
        apply mul_left_cancel₀ hπ
        calc
          _ = (2*Real.pi*k/p)*((p:ℝ)*n) := by field_simp
          _ = (2*m*Real.pi-2*Real.pi*j/n)*((p:ℝ)*n) := congrArg (fun x : ℝ => x*((p:ℝ)*n)) hm
          _ = _ := by field_simp
      have hei : (n:ℤ)*(k:ℤ)=(p:ℤ)*(m*(n:ℤ)-j) := by exact_mod_cast he
      exact ⟨m*(n:ℤ)-j,hei⟩
  have hdivn : p∣n*k := by exact_mod_cast hdiv
  exact hc.dvd_of_dvd_mul_right hdivn

/-- Exact cosine realization of the inward odd-grid coordinate. -/
theorem forbidden_cosine_grid_identity {n : ℕ} (hn : Odd n) :
    Real.cos (2*Real.pi*((n-1)/2:ℕ)/n)= -Real.cos (Real.pi/n) := by
  have hn0 : 0<n := Nat.pos_of_ne_zero (by intro h; simp [h] at hn)
  have hne : (n:ℝ)≠0 := by exact_mod_cast hn0.ne'
  have he : 2*((n-1)/2)+1=n := by rcases hn with ⟨k,hk⟩; omega
  have her : (2:ℝ)*((n-1)/2:ℕ)+1=n := by exact_mod_cast he
  have ha : 2*Real.pi*((n-1)/2:ℕ)/n=Real.pi-Real.pi/n := by
    apply (div_eq_iff hne).mpr
    field_simp
    nlinarith
  rw [ha,Real.cos_pi_sub]

/-- No smaller positive grid order represents the inward first cosine. -/
theorem forbidden_cosine_least_order {n l : ℕ} (hn : Odd n) (hl : 0<l) (j : ℤ)
    (hj : Real.cos (2*Real.pi*j/l)= -Real.cos (Real.pi/n)) : n∣l := by
  rw [←forbidden_cosine_grid_identity hn] at hj
  exact coprime_dvd_of_grid_cos_eq
    (Nat.pos_of_ne_zero (by intro h; simp [h] at hn)) (forbidden_half_coprime hn) hl j hj

/-- The exact paired candidate lies on the stated odd mesh. Primality is not
needed here: every odd positive base order has this construction. -/
theorem forbidden_pair_grid {q : ℕ} (hq : Odd q) (k m : ℕ) :
    (-Real.cos (Real.pi/(q*(2*m+1):ℕ)),Real.cos (primePhase q k)) ∈
      orderCosineGrid (q*(2*m+1)) := by
  have hq0 : 0<q := Nat.pos_of_ne_zero (by intro h; simp [h] at hq)
  have hqne : (q:ℝ)≠0 := by exact_mod_cast hq0.ne'
  have hmne : (2*(m:ℝ)+1)≠0 := by positivity
  have hn : Odd (q*(2*m+1)) := hq.mul ⟨m,rfl⟩
  refine ⟨(((q*(2*m+1)-1)/2:ℕ):ℤ),(k:ℤ)*(2*(m:ℤ)+1),?_⟩
  apply Prod.ext
  · simpa only [Int.cast_natCast] using (forbidden_cosine_grid_identity hn).symm
  · dsimp
    congr 1
    unfold primePhase
    push_cast
    field_simp

/-- The stated mesh is the least positive order of the paired candidate. -/
theorem forbidden_pair_least_grid {q l : ℕ} (hq : Odd q) (k m : ℕ) (hl : 0<l)
    (hgrid : (-Real.cos (Real.pi/(q*(2*m+1):ℕ)),Real.cos (primePhase q k))∈orderCosineGrid l) :
    q*(2*m+1)∣l ∧ q*(2*m+1)≤l := by
  rcases hgrid with ⟨j,k',he⟩
  have he1 := congrArg Prod.fst he
  have hd := forbidden_cosine_least_order (hq.mul (show Odd (2*m+1) from ⟨m,rfl⟩)) hl j he1.symm
  exact ⟨hd,Nat.le_of_dvd hl hd⟩

end
end IsingBulk.Anisotropic
