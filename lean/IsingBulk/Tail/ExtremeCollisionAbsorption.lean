import IsingBulk.Tail.GlobalGeometry

/-! Conservative collision power for extreme-coordinate coarea after
integrating remaining coordinates on a fixed cube. This deliberately
forgoes the polar d^(N−2) volume gain while preserving the source endpoint. -/
namespace IsingBulk.Tail
noncomputable section

def extremeCollisionPower (N j : ℕ) : ℕ := N*(N-1)-2*j-4

theorem extremeCollisionPower_source_lower {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) : 3*(2*p)≤extremeCollisionPower N j := by
  have hs : 2≤(2*p)^2 := by nlinarith
  have hj' : 2*j+2≤(2*p)^2 := by omega
  have hNp : 2*p+1≤N-1 := by omega
  have hh := Nat.mul_le_mul hN hNp
  have hpoly : (2*p)^2+3*(2*p)+2≤N*(N-1) := by nlinarith
  unfold extremeCollisionPower
  omega

theorem extremeCollisionPower_source_identity {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) :
    extremeCollisionPower N j+2*j+4+N=N^2 := by
  have hl := extremeCollisionPower_source_lower hp hN hj
  have hpred : N-1+1=N := by omega
  have hid : N*(N-1)+N=N^2 := by nlinarith
  unfold extremeCollisionPower at hl ⊢
  omega

theorem extremeCollisionPower_source_ge_N {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) : N≤extremeCollisionPower N j := by
  have hs : 2≤(2*p)^2 := by nlinarith
  have hj' : 2*j+2≤(2*p)^2 := by omega
  have hN2 : 2*p≤N-2 := by omega
  have hprod := Nat.mul_le_mul hN hN2
  have hpred : N-1+1=N := by omega
  have hpred2 : N-2+2=N := by omega
  have hpoly : N+2*j+4≤N*(N-1) := by nlinarith
  unfold extremeCollisionPower
  omega

theorem extremeCollisionPower_source_quadratic {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) :
    N^2≤(2*((2*p)^2/2-1)+6)*extremeCollisionPower N j := by
  have hL := extremeCollisionPower_source_ge_N hp hN hj
  have hid := extremeCollisionPower_source_identity hp hN hj
  have hL1 : 1≤extremeCollisionPower N j := by omega
  nlinarith

/-- One exponent K0 is fixed before N and epsilon. It absorbs even an
exp(A N²) cost after discarding the remaining-coordinate volume gain. -/
theorem extreme_collision_polynomial_absorption (p : ℕ) (hp : 1≤p) (A : ℝ) (hA : 0≤A) :
    ∃ K₀ : ℝ, 1<K₀ ∧ ∀ N j : ℕ, 2*p+2≤N → j≤(2*p)^2/2-1 →
      ∀ d : ℝ, 0≤d → d≤(N:ℝ)^(-K₀) →
        Real.exp (A*(N:ℝ)^2)*d^(extremeCollisionPower N j)≤1 := by
  let J := (2*p)^2/2-1
  let M : ℝ := (2*J+6:ℕ)
  have hM : 0<M := by dsimp [M]; positivity
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K₀ := 1+M*(A+1)/Real.log 2
  have hK : 1<K₀ := by
    have hh : 0<M*(A+1)/Real.log 2 := by positivity
    dsimp [K₀]
    linarith
  have hK0 : 0≤K₀ := by linarith
  have hKlog : M*A≤K₀*Real.log 2 := by
    have he : K₀*Real.log 2=Real.log 2+M*(A+1) := by dsimp [K₀]; field_simp
    rw [he]
    nlinarith
  refine ⟨K₀,hK,?_⟩
  intro N j hN hj d hd hdb
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn2 : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  have hlog : Real.log 2≤Real.log N := Real.log_le_log (by norm_num) hn2
  have hratio : (N:ℝ)^2≤M*(extremeCollisionPower N j:ℝ) := by
    dsimp [M,J]
    exact_mod_cast extremeCollisionPower_source_quadratic hp hN hj
  have hKlogN : M*A≤K₀*Real.log N := hKlog.trans (mul_le_mul_of_nonneg_left hlog hK0)
  have hexp : A*(N:ℝ)^2+(extremeCollisionPower N j:ℝ)*(Real.log N*(-K₀))≤0 := by
    have h₁ := mul_le_mul_of_nonneg_left hratio hA
    have h₂ := mul_le_mul_of_nonneg_right hKlogN (Nat.cast_nonneg (extremeCollisionPower N j))
    nlinarith
  calc
    _ ≤ Real.exp (A*(N:ℝ)^2)*((N:ℝ)^(-K₀))^(extremeCollisionPower N j) := by gcongr
    _ = Real.exp (A*(N:ℝ)^2+(extremeCollisionPower N j:ℝ)*(Real.log N*(-K₀))) := by
      rw [Real.rpow_def_of_pos hn,← Real.exp_nat_mul,Real.exp_add]
    _ ≤ 1 := Real.exp_le_one_iff.mpr hexp


/-- Current fields leave the distinguished coordinate fixed. Only free-free
zeros are counted; coarea and puncture removal use separate one-power and two-power
losses, so the conservative shared allowance here is two, not four. -/
def freeExtremeCollisionPower (N j : ℕ) : ℕ := (N-1)*(N-2)-2*j-2

theorem freeExtremeCollisionPower_source_ge {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) :
    N-2≤freeExtremeCollisionPower N j ∧ 2*p≤freeExtremeCollisionPower N j := by
  have hs : 2≤(2*p)^2 := by nlinarith
  have hj' : 2*j+2≤(2*p)^2 := by omega
  have hNm : 2*p≤N-2 := by omega
  have hpred : N-2+1=N-1 := by omega
  have hsq : (2*p)^2≤(N-2)^2 := by nlinarith
  have hprod : N-2+2*j+2≤(N-1)*(N-2) := by nlinarith
  unfold freeExtremeCollisionPower
  omega

theorem freeExtremeCollisionPower_source_identity {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) :
    freeExtremeCollisionPower N j+3*N+2*j=N^2 := by
  have hh := freeExtremeCollisionPower_source_ge hp hN hj
  have hpred : N-1+1=N := by omega
  have hpred2 : N-2+2=N := by omega
  have he : (N-1)*(N-2)+3*N=N^2+2 := by nlinarith
  unfold freeExtremeCollisionPower at hh ⊢
  omega

theorem freeExtremeCollisionPower_source_quadratic {p N j : ℕ} (hp : 1≤p)
    (hN : 2*p+2≤N) (hj : j≤(2*p)^2/2-1) :
    N^2≤(2*((2*p)^2/2-1)+7)*freeExtremeCollisionPower N j := by
  obtain ⟨hL,hL'⟩ := freeExtremeCollisionPower_source_ge hp hN hj
  have hN2 : N≤2*freeExtremeCollisionPower N j := by omega
  have hid := freeExtremeCollisionPower_source_identity hp hN hj
  have hL1 : 1≤freeExtremeCollisionPower N j := by omega
  nlinarith

theorem collision_absorption_of_quadratic_ratio (A M : ℝ) (hA : 0≤A) (hM : 0<M) :
    ∃ K₀ : ℝ, 1<K₀ ∧ ∀ N L : ℕ, 2≤N → (N:ℝ)^2≤M*(L:ℝ) →
      ∀ d : ℝ, 0≤d → d≤(N:ℝ)^(-K₀) → Real.exp (A*(N:ℝ)^2)*d^L≤1 := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K₀ := 1+M*(A+1)/Real.log 2
  have hK : 1<K₀ := by
    have hh : 0<M*(A+1)/Real.log 2 := by positivity
    dsimp [K₀]
    linarith
  have hK0 : 0≤K₀ := by linarith
  have hKlog : M*A≤K₀*Real.log 2 := by
    have he : K₀*Real.log 2=Real.log 2+M*(A+1) := by dsimp [K₀]; field_simp
    rw [he]
    nlinarith
  refine ⟨K₀,hK,?_⟩
  intro N L hN hratio d hd hdb
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn2 : (2:ℝ)≤N := by exact_mod_cast hN
  have hlog : Real.log 2≤Real.log N := Real.log_le_log (by norm_num) hn2
  have hKlogN : M*A≤K₀*Real.log N := hKlog.trans (mul_le_mul_of_nonneg_left hlog hK0)
  have hexp : A*(N:ℝ)^2+(L:ℝ)*(Real.log N*(-K₀))≤0 := by
    have h₁ := mul_le_mul_of_nonneg_left hratio hA
    have h₂ := mul_le_mul_of_nonneg_right hKlogN (Nat.cast_nonneg L)
    nlinarith
  calc
    _ ≤ Real.exp (A*(N:ℝ)^2)*((N:ℝ)^(-K₀))^L := by gcongr
    _ = Real.exp (A*(N:ℝ)^2+(L:ℝ)*(Real.log N*(-K₀))) := by
      rw [Real.rpow_def_of_pos hn,← Real.exp_nat_mul,Real.exp_add]
    _ ≤ 1 := Real.exp_le_one_iff.mpr hexp

theorem free_extreme_collision_polynomial_absorption (p : ℕ) (hp : 1≤p) (A : ℝ) (hA : 0≤A) :
    ∃ K₀ : ℝ, 1<K₀ ∧ ∀ N j : ℕ, 2*p+2≤N → j≤(2*p)^2/2-1 →
      ∀ d : ℝ, 0≤d → d≤(N:ℝ)^(-K₀) →
        Real.exp (A*(N:ℝ)^2)*d^(freeExtremeCollisionPower N j)≤1 := by
  obtain ⟨K,hK,hbound⟩ := collision_absorption_of_quadratic_ratio A
    (2*((2*p)^2/2-1)+7:ℕ) hA (by positivity)
  refine ⟨K,hK,?_⟩
  intro N j hN hj d hd hdb
  apply hbound N (freeExtremeCollisionPower N j) (by omega) _ d hd hdb
  exact_mod_cast freeExtremeCollisionPower_source_quadratic hp hN hj

end
end IsingBulk.Tail
