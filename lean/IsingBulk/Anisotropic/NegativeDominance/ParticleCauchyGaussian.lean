import IsingBulk.Anisotropic.NegativeDominance.ParticleGaussian
import IsingBulk.Anisotropic.NegativeDominance.GaussianMoment

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges

/-- Actual c/N Cauchy envelopes retain coefficient one on j log N. -/
theorem particle_cauchy_gaussian_bound {r C M δ K : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hδ : 0<δ) (hK : 0<K) :
    ∃a L : ℝ,0<a ∧ 0<L ∧ ∀N : ℕ,1≤N → ∀j : ℕ,
      K*particleEdgeMajorant r C M N*((N : ℝ)/δ)^j≤
        Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+L*((j : ℝ)+1)) := by
  obtain ⟨a,E,ha,hE,hbound⟩ := particleEdgeMajorant_gaussian hr hr1 hC hM
  let L : ℝ := 1+|Real.log K|+E+|Real.log δ|
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨a,L,ha,hL,fun N hN j => ?_⟩
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hlogN : 0≤Real.log (N : ℝ) := Real.log_nonneg hN1
  have hpow : ((N : ℝ)/δ)^j=Real.exp ((j : ℝ)*(Real.log N-Real.log δ)) := by
    rw [←Real.log_div hNp.ne' hδ.ne',Real.exp_nat_mul,Real.exp_log (div_pos hNp hδ)]
  have hconst : Real.log K+E≤L := by
    dsimp [L]
    linarith only [le_abs_self (Real.log K),abs_nonneg (Real.log δ)]
  have hdelta : -Real.log δ≤L := by
    dsimp [L]
    linarith only [neg_le_abs (Real.log δ),abs_nonneg (Real.log K),hE.le]
  have hjdelta := mul_le_mul_of_nonneg_left hdelta (Nat.cast_nonneg j)
  calc
    _≤K*Real.exp (-a*(N : ℝ)^2+E)*((N : ℝ)/δ)^j := by gcongr; exact hbound N
    _=Real.exp (Real.log K+(-a*(N : ℝ)^2+E)+(j : ℝ)*(Real.log N-Real.log δ)) := by
      simp only [Real.exp_add,Real.exp_log hK,hpow]
    _≤_ := Real.exp_le_exp.mpr (by nlinarith only [hconst,hjdelta,hlogN])

/-- Complete infinite sums of all c/N Cauchy envelopes, without a finite
particle truncation or an assumed summability estimate. -/
theorem particle_cauchy_gaussian_sum {r C M δ K : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hδ : 0<δ) (hK : 0<K) :
    ∃D L : ℝ,0<D ∧ 0<L ∧ ∀j : ℕ,
      Summable (fun N : ℕ => if N=0 then 0 else K*particleEdgeMajorant r C M N*((N : ℝ)/δ)^j) ∧
      (∑' N : ℕ, if N=0 then 0 else K*particleEdgeMajorant r C M N*((N : ℝ)/δ)^j)≤
        D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+L*((j : ℝ)+1)) := by
  obtain ⟨a,L,ha,hL,hb⟩ := particle_cauchy_gaussian_bound hr hr1 hC hM hδ hK
  obtain ⟨D,hD,hDsum⟩ := gaussian_log_moment_sum ha L
  refine ⟨D,L+|Real.log a|/2,hD,by positivity,fun j => ?_⟩
  have hbound (N : ℕ) :
      (if N=0 then 0 else K*particleEdgeMajorant r C M N*((N : ℝ)/δ)^j)≤
        Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+L*((j : ℝ)+1)) := by
    split
    · exact (Real.exp_pos _).le
    · exact hb N (by omega) j
  have hnonneg (N : ℕ) : 0 ≤ (if N=0 then 0 else K*particleEdgeMajorant r C M N*((N : ℝ)/δ)^j) := by
    split
    · rfl
    · exact mul_nonneg (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le N)) (by positivity)
  have hs := (hDsum j).1.of_nonneg_of_le hnonneg hbound
  exact ⟨hs,(hs.tsum_le_tsum hbound (hDsum j).1).trans (hDsum j).2⟩

end
end IsingBulk.Anisotropic.NegativeDominance
