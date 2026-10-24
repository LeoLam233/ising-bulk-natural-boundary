import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles
import IsingBulk.Anisotropic.RegularEdges.UpperFullIntegrandBound

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set

theorem negativeShiftedFullIntegrand_uniform_jets_upper {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ ε : ℂ, 0<ε.im → ‖ε‖<δ → ∀ (m k : ℕ) [Nonempty (Fin m)]
        (v : Fin (m+k) → ℝ), (∀ i, v i∈Icc (-Real.pi) Real.pi) →
        (fun i : Fin m => v (Fin.castAdd k i))≠0 →
        ‖iteratedDeriv j (fun u => negativeShiftedFullIntegrand b B S (m+k) u v)
          ε‖≤D*particleEdgeMajorant r C M (m+k+1)*(m+k+1 : ℕ)^j*
            (1+‖fun i : Fin m => v (Fin.castAdd k i)‖^(-(2*(j+1) : ℝ))) := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,h⟩ := edgeFullIntegrand_uniform_jets_upper hb hB hc hS hS0 j
  refine ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,?_⟩
  intro ε hε he m k _ v hv hv0
  have hn := negativeShiftedAngles_retained_norm m k v hv
  have hp : (fun i : Fin m => negativeShiftedAngles (m+k) v ((Fin.castAdd k i).castSucc))≠0 := by
    intro hz
    have hn0 : ‖fun i : Fin m => v (Fin.castAdd k i)‖=0 := by rw [← hn,hz,norm_zero]
    exact hv0 (norm_eq_zero.mp hn0)
  have hh := h ε hε he (m+k+1) m (negativeShiftedAngles (m+k) v)
    (fun i => (Fin.castAdd k i).castSucc) (fun _ => wrapAngle_mem _) hp
  rw [hn] at hh
  exact hh

end
end IsingBulk.Anisotropic.NegativeDominance
