import IsingBulk.Tail.MixedAmplitudeScalarJets
import IsingBulk.Tail.ScaledAnalyticProductJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped Topology BigOperators ContDiff

def mixedActiveSmoothAmplitude {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  ((∏ i,mixedActiveAmplitudeVertex J q s φ y 1 i u)+
    (∏ i,mixedActiveAmplitudeVertex J q s φ y 2 i u))*
    ∏ i,mixedActiveAmplitudeVertex J q s φ y 0 i u

theorem analytic_two_product_amplitude_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (f : Fin 3 → Fin N → E → ℂ) (x : E) (order : ℕ) {C : ℝ} (hC : 0≤C)
    (hf : ∀ a i,JetBound (f a i) x order C) :
    let F := fun u => ((∏ i,f 1 i u)+(∏ i,f 2 i u))*∏ i,f 0 i u
    AnalyticAt ℂ F x ∧ ∀ k≤order,‖iteratedFDeriv ℂ k F x‖≤
      2*(2^order*C*C)^N*(N:ℝ)^k := by
  let g := fun a : Fin 3 => fun i : Fin N => fun u : E => f a i u*f 0 i u
  have hg (a : Fin 3) (i : Fin N) : JetBound (g a i) x order (2^order*C*C) :=
    (hf a i).mul (hf 0 i)
  have hpA (a : Fin 3) : AnalyticAt ℂ (fun u => ∏ i,g a i u) x :=
    Finset.analyticAt_fun_prod _ (fun i _ => (hg a i).analytic)
  have hp (a : Fin 3) (k : ℕ) (hk : k≤order) :
      ‖iteratedFDeriv ℂ k (fun u => ∏ i,g a i u) x‖≤(2^order*C*C)^N*(N:ℝ)^k := by
    have hh := analytic_finset_product_geometric_jets Finset.univ (g a) x order (2^order*C*C) 1
      (by positivity) (by norm_num) (fun i _ => (hg a i).analytic)
      (fun i _ l hl => by simpa using (hg a i).bound l hl) k hk
    simpa using hh
  have he : (fun u => ((∏ i,f 1 i u)+(∏ i,f 2 i u))*∏ i,f 0 i u)=
      (fun u => (∏ i,g 1 i u)+(∏ i,g 2 i u)) := by
    funext u
    simp only [g,Finset.prod_mul_distrib,add_mul]
  dsimp only
  rw [he]
  refine ⟨(hpA 1).add (hpA 2),?_⟩
  intro k hk
  change ‖iteratedFDeriv ℂ k ((fun u => ∏ i,g 1 i u)+(fun u => ∏ i,g 2 i u)) x‖≤_
  rw [iteratedFDeriv_add_apply (hpA 1).contDiffAt (hpA 2).contDiffAt]
  exact (norm_add_le _ _).trans ((add_le_add (hp 1 k hk) (hp 2 k hk)).trans_eq (by ring))

theorem mixedActiveSmoothAmplitude_jets {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (order : ℕ) {C : ℝ} (hC : 0≤C)
    (hf : ∀ a i,JetBound (mixedActiveAmplitudeVertex J q s φ y a i) 0 order C) :
    AnalyticAt ℂ (mixedActiveSmoothAmplitude J q s φ y) 0 ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k (mixedActiveSmoothAmplitude J q s φ y) 0‖≤
        2*(2^order*C*C)^N*(N:ℝ)^k :=
  analytic_two_product_amplitude_jets (mixedActiveAmplitudeVertex J q s φ y) 0 order hC hf

end
end IsingBulk.Tail
