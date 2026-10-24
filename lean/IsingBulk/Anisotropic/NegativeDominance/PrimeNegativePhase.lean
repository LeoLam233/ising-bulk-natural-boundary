import IsingBulk.Anisotropic.RegularEdges.PhasePrime
import IsingBulk.Anisotropic.NegativeNormalForm.ResonantKernel

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open RegularEdges NegativeNormalForm

theorem exists_prime_negative_phase {b : ℝ} (hb : b∈primePhaseCosines) :
    ∃ p : ℕ, ∃ phi : ℝ, p.Prime ∧ Odd p ∧ 0<phi ∧ phi<Real.pi ∧
      Real.sin phi≠0 ∧ b=Real.cos phi ∧
      IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (b:ℂ)) p ∧
      ∀ N : ℕ,p∣N → Complex.exp ((N:ℂ)*((phi:ℂ)*Complex.I))=1 := by
  obtain ⟨p,k,hp,ho,hk,hkp,hb⟩ := (mem_primePhaseCosines_iff b).mp hb
  have hbounds := primePhase_bounds hp hk hkp
  refine ⟨p,primePhase p k,hp,ho,hbounds.1,hbounds.2,
    (Real.sin_pos_of_pos_of_lt_pi hbounds.1 hbounds.2).ne',hb,?_,?_⟩
  · rw [hb,continuedRoot_primePhase hp hk hkp]
    exact primePhaseRoot_isPrimitiveRoot hp hk (by omega)
  · intro N hN
    obtain ⟨q,rfl⟩ := hN
    exact rational_phase_resonance p q k hp.ne_zero

end
end IsingBulk.Anisotropic.NegativeDominance
