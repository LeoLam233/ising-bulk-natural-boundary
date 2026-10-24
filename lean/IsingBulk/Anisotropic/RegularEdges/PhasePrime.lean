import IsingBulk.Anisotropic.RegularEdges.PhaseJets
import IsingBulk.Anisotropic.Geometry.PrimePhases

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.Tail

theorem continuedRoot_cos_formula {φ : ℝ} (hφ : 0<φ) (hπ : φ<Real.pi) :
    continuedRoot (Real.cos φ:ℂ)=Complex.exp (-Complex.I*(φ:ℂ)) := by
  have hb : |Real.cos φ|<1 := by
    refine abs_lt.mpr ⟨?_,?_⟩
    · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hφ.le le_rfl hπ
    · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hφ
  rw [continuedRoot_real_formula hb,←Real.sin_eq_sqrt_one_sub_cos_sq hφ.le hπ.le]
  rw [show -Complex.I*(φ:ℂ)=(-(φ:ℂ))*Complex.I by ring,Complex.exp_mul_I]
  simp only [Complex.cos_neg,Complex.sin_neg,Complex.ofReal_cos,Complex.ofReal_sin]
  ring

theorem continuedRoot_primePhase {p k : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : 2*k<p) :
    continuedRoot (Real.cos (primePhase p k):ℂ)=primePhaseRoot p k :=
  continuedRoot_cos_formula (primePhase_bounds hp hk hkp).1 (primePhase_bounds hp hk hkp).2

theorem continuedRoot_primePhase_pow_iff {p k N : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : 2*k<p) :
    continuedRoot (Real.cos (primePhase p k):ℂ)^N=1 ↔ p∣N := by
  rw [continuedRoot_primePhase hp hk hkp]
  exact primePhaseRoot_pow_eq_one_iff hp hk (by omega)

/-- Dense prime cosine values have the exact first HT resonance and its derivative order. -/
theorem primeCosine_first_odd {b : ℝ} (hb : b∈primePhaseCosines) :
    ∃q j : ℕ,1≤q ∧ 2*j+1=(2*q+1)^2 ∧ continuedRoot (b:ℂ)^(2*q+1)=1 ∧
      ∀i<q,continuedRoot (b:ℂ)^(2*i+1)≠1 := by
  obtain ⟨p,k,hp,ho,hk,hkp,rfl⟩ := (mem_primePhaseCosines_iff b).mp hb
  obtain ⟨q,hq⟩ := ho
  have hpq : p=2*q+1 := by omega
  have hqpos : 1≤q := by have := hp.two_le; omega
  refine ⟨q,2*q*(q+1),hqpos,by ring,?_,?_⟩
  · rw [continuedRoot_primePhase_pow_iff hp hk hkp,←hpq]
  · intro i hi h
    have hd := (continuedRoot_primePhase_pow_iff hp hk hkp).mp h
    have := Nat.le_of_dvd (by omega : 0<2*i+1) hd
    omega

/-- The first LT resonance at a primitive odd-prime phase is twice that prime. -/
theorem primeCosine_first_even {b : ℝ} (hb : b∈primePhaseCosines) :
    ∃q j : ℕ,2*(j+1)=(2*q+2)^2 ∧ continuedRoot (b:ℂ)^(2*q+2)=1 ∧
      ∀i<q,continuedRoot (b:ℂ)^(2*i+2)≠1 := by
  obtain ⟨p,k,hp,ho,hk,hkp,rfl⟩ := (mem_primePhaseCosines_iff b).mp hb
  have hsub : p-1+1=p := Nat.sub_add_cancel hp.one_le
  have hprod : 1≤2*p*p := by have := hp.two_le; nlinarith
  have hj : 2*p*p-1+1=2*p*p := Nat.sub_add_cancel hprod
  refine ⟨p-1,2*p*p-1,by nlinarith,?_,?_⟩
  · rw [continuedRoot_primePhase hp hk hkp]
    convert (primePhaseRoot_first_positive_even hp ho hk (by omega)).2.1 using 1
    congr 1
    omega
  · intro i hi h
    rw [continuedRoot_primePhase hp hk hkp] at h
    exact (primePhaseRoot_first_positive_even hp ho hk (by omega)).2.2 (2*i+2)
      (by exact ⟨i+1,by omega⟩) (by omega) (by omega) h

end
end IsingBulk.Anisotropic.RegularEdges
