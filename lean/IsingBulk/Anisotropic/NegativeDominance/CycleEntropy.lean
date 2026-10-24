import IsingBulk.Anisotropic.NegativeDominance.CycleEnvelope

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

def cycleFixedLoss (ρ M c L K σ : ℝ) : ℝ :=
  1+|Real.log (2*K/c)|+2*|Real.log M|+|Real.log L|+|Real.log (2*ρ)|+
    |Real.log (8/σ)|+Real.log 2

theorem cycleFixedLoss_pos (ρ M c L K σ : ℝ) : 0<cycleFixedLoss ρ M c L K σ := by
  unfold cycleFixedLoss
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- Exact Taylor-order strength of the Stokes error before absorbing only
its order-independent entropy. -/
theorem cycleErrorEnvelope_log_bound (ρ M c L K σ : ℝ) {m : ℕ} (j : ℕ)
    (hρ : 0<ρ) (hM : 0<M) (hc : 0<c) (hL : 0<L) (hK : 0<K) (hσ : 0<σ) (hm : 0<m) :
    Real.log (cycleErrorEnvelope ρ M c L K σ m j)≤
      -(Real.log 2/2)*(2*(m : ℝ)+1)^2+
      (2*m+1)*Real.log (2*(m : ℝ)+2)+cycleFixedLoss ρ M c L K σ*(2*m+1)+
      ((j : ℝ)+1)*(Real.log (2*(m : ℝ)+1)+cycleFixedLoss ρ M c L K σ) := by
  let N : ℝ := 2*(m : ℝ)+1
  let D := cycleFixedLoss ρ M c L K σ
  have hmR : (1 : ℝ)≤m := by exact_mod_cast hm
  have hN1 : 1≤N := by dsimp [N]; linarith
  have hN0 : 0≤N := by linarith
  have hconst : Real.log (2*K/c)≤N*|Real.log (2*K/c)| :=
    (le_abs_self _).trans (le_mul_of_one_le_left (abs_nonneg _) hN1)
  have hMt : (3*(m : ℝ)+2)*Real.log M≤2*N*|Real.log M| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self (Real.log M)) (show 0≤3*(m : ℝ)+2 by positivity)
    have hh' := mul_le_mul_of_nonneg_right (show 3*(m : ℝ)+2≤2*N by dsimp [N]; linarith) (abs_nonneg (Real.log M))
    exact hh.trans hh'
  have hLt : 2*(m : ℝ)*Real.log L≤N*|Real.log L| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self (Real.log L)) (show 0≤2*(m : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right (show 2*(m : ℝ)≤N by dsimp [N]; linarith) (abs_nonneg (Real.log L))
    exact hh.trans hh'
  have hρt : 2*(m : ℝ)*Real.log (2*ρ)≤N*|Real.log (2*ρ)| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2*ρ))) (show 0≤2*(m : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right (show 2*(m : ℝ)≤N by dsimp [N]; linarith) (abs_nonneg (Real.log (2*ρ)))
    exact hh.trans hh'
  have hlog : Real.log (2*(m : ℝ))≤Real.log (N+1) :=
    Real.log_le_log (by positivity) (by dsimp [N]; linarith)
  have hlogN : 0≤Real.log (N+1) := Real.log_nonneg (by linarith)
  have hshape : (m : ℝ)*Real.log (2*(m : ℝ))≤N*Real.log (N+1) :=
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) hlogN)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hD8 : Real.log (8/σ)≤D := by
    dsimp [D,cycleFixedLoss]
    linarith only [le_abs_self (Real.log (8/σ)),abs_nonneg (Real.log (2*K/c)),
      abs_nonneg (Real.log M),abs_nonneg (Real.log L),abs_nonneg (Real.log (2*ρ)),hl2]
  have hj := mul_le_mul_of_nonneg_left hD8 (show 0≤(j : ℝ)+1 by positivity)
  have hextra : 0≤N*(1+|Real.log (8/σ)|) := by positivity
  have hl2N : 0≤N*Real.log 2 := mul_nonneg hN0 hl2
  rw [cycleErrorEnvelope_log ρ M c L K σ j hρ hM hc hL hK hσ hm]
  rw [show 2*(m : ℝ)+2=(2*(m : ℝ)+1)+1 by ring]
  change _≤-(Real.log 2/2)*N^2+N*Real.log (N+1)+D*N+((j : ℝ)+1)*(Real.log N+D)
  dsimp [D,cycleFixedLoss,N] at hconst hMt hLt hρt hshape hj hextra hl2N ⊢
  nlinarith only [hconst,hMt,hLt,hρt,hshape,hj,hextra,hl2N]

/-- A common threshold for every Taylor order, with the sharp j log N loss. -/
theorem eventually_cycleErrorEnvelope_bound (ρ M c L K σ : ℝ)
    (hρ : 0<ρ) (hM : 0<M) (hc : 0<c) (hL : 0<L) (hK : 0<K) (hσ : 0<σ) :
    ∃N₀ : ℕ, ∀m : ℕ, N₀≤2*m+1 → 0<m → ∀j : ℕ,
      cycleErrorEnvelope ρ M c L K σ m j≤
        Real.exp (-(Real.log 2/4)*(2*(m : ℝ)+1)^2+
          ((j : ℝ)+1)*Real.log (2*(m : ℝ)+1)+cycleFixedLoss ρ M c L K σ*((j : ℝ)+1)) := by
  have hD := cycleFixedLoss_pos ρ M c L K σ
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_gaussian_entropy_absorb (Real.log 2/2) 1 (cycleFixedLoss ρ M c L K σ)
      (by positivity) (by norm_num) hD.le)
  refine ⟨N₀,fun m hm₀ hm j => ?_⟩
  have hE := hN₀ (2*m+1) hm₀
  push_cast at hE
  rw [show 2*(m : ℝ)+1+1=2*(m : ℝ)+2 by ring] at hE
  have hbound := cycleErrorEnvelope_log_bound ρ M c L K σ j hρ hM hc hL hK hσ hm
  have hpos : 0<cycleErrorEnvelope ρ M c L K σ m j := by
    rw [cycleErrorEnvelope_factor]
    positivity
  apply (Real.log_le_iff_le_exp hpos).mp
  nlinarith only [hE,hbound,hD.le]

/-- All odd indices, not only an eventual range; zero cutoff-gradient cost
is also allowed. -/
theorem cycleErrorEnvelope_global_bound (ρ M c L K σ : ℝ)
    (hρ : 0<ρ) (hM : 0<M) (hc : 0<c) (hL : 0<L) (hK : 0≤K) (hσ : 0<σ) :
    ∃C : ℝ,0<C ∧ ∀m : ℕ,0<m → ∀j : ℕ,
      cycleErrorEnvelope ρ M c L K σ m j≤
        Real.exp (-(Real.log 2/4)*(2*(m : ℝ)+1)^2+
          ((j : ℝ)+1)*Real.log (2*(m : ℝ)+1)+C*((j : ℝ)+1)) := by
  by_cases hKp : 0<K
  · have hD := cycleFixedLoss_pos ρ M c L K σ
    have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨E,hE,hEg⟩ := gaussian_entropy_global (Real.log 2/2) 1 (cycleFixedLoss ρ M c L K σ)
      (by positivity) (by norm_num) hD.le
    refine ⟨cycleFixedLoss ρ M c L K σ+E,by positivity,fun m hm j => ?_⟩
    have he := hEg (2*m+1)
    push_cast at he
    rw [show 2*(m : ℝ)+1+1=2*(m : ℝ)+2 by ring] at he
    have hb := cycleErrorEnvelope_log_bound ρ M c L K σ j hρ hM hc hL hKp hσ hm
    have hpos : 0<cycleErrorEnvelope ρ M c L K σ m j := by
      rw [cycleErrorEnvelope_factor]
      positivity
    apply (Real.log_le_iff_le_exp hpos).mp
    have hEj : 0≤E*(j : ℝ) := by positivity
    nlinarith only [he,hb,hD.le,hEj]
  · have hK0 : K=0 := le_antisymm (not_lt.mp hKp) hK
    subst K
    refine ⟨1,by norm_num,fun m _ j => ?_⟩
    simp only [cycleErrorEnvelope,mul_zero,zero_mul,Real.exp_nonneg]

end
end IsingBulk.Anisotropic.NegativeDominance
