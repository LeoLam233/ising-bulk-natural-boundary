import IsingBulk.Anisotropic.Geometry.PrimePhases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace IsingBulk.Anisotropic
noncomputable section

def orderCosineGrid (n : ℕ) : Set (ℝ × ℝ) :=
  {uv | ∃j k : ℤ, uv=(Real.cos (2*Real.pi*j/n),Real.cos (2*Real.pi*k/n))}

theorem even_of_grid_cos_eq_neg_one {n : ℕ} (hn : 0<n) (j : ℤ)
    (hj : Real.cos (2*Real.pi*j/n)= -1) : Even n := by
  rcases Real.cos_eq_neg_one_iff.mp hj with ⟨k,hk⟩
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (2:ℝ)*j=(2*k+1)*(n:ℝ) := by
    have h := (eq_div_iff hn0).mp hk
    nlinarith [Real.pi_pos]
  have hei : (2:ℤ)*j=(2*k+1)*(n:ℤ) := by exact_mod_cast he
  have hp : Even ((2*k+1)*(n:ℤ)) := hei ▸ even_two_mul j
  have ho : Odd (2*k+1) := ⟨k,by ring⟩
  have hne : Even (n:ℤ) := (Int.even_mul.mp hp).resolve_left (Int.not_even_iff_odd.mpr ho)
  exact_mod_cast hne

theorem no_odd_negative_endpoint_grid {n : ℕ} (hn : Odd n) {uv : ℝ × ℝ}
    (hgrid : uv∈orderCosineGrid n) : uv.1≠ -1 ∧ uv.2≠ -1 := by
  have hn0 : 0<n := Nat.pos_of_ne_zero (by intro h; simp [h] at hn)
  rcases hgrid with ⟨j,k,rfl⟩
  exact ⟨fun h => (Nat.not_even_iff_odd.mpr hn) (even_of_grid_cos_eq_neg_one hn0 j h),
    fun h => (Nat.not_even_iff_odd.mpr hn) (even_of_grid_cos_eq_neg_one hn0 k h)⟩


/-- A primitive prime cosine cannot occur on a grid of nonmultiple order. -/
theorem prime_dvd_of_grid_cos_eq {p k n : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : k<p)
    (hn : 0<n) (j : ℤ)
    (hj : Real.cos (2*Real.pi*j/n)=Real.cos (primePhase p k)) : p∣n := by
  obtain ⟨m,hm⟩ := Real.cos_eq_cos_iff.mp hj
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
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
  exact (hp.dvd_mul.mp hdivn).resolve_right (Nat.not_dvd_of_pos_of_lt hk hkp)

end
end IsingBulk.Anisotropic
