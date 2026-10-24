import IsingBulk.Anisotropic.NegativeCycles.ActualInnerRemainder
import IsingBulk.Anisotropic.NegativeCycles.CompactRemainderJets

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric MeasureTheory NegativeNormalForm
set_option maxHeartbeats 800000

/-- Uniform actual inner remainder integration, including exact all-order jet
exchange. Geometric angle maps and the actual pole enter explicitly. -/
theorem exists_actual_inner_integral (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) :
    ∃ (R₀ : ℂ → ℂ) (r c σ C M : ℝ), 0<r ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ m : ℕ, ∀ (K : Set (Fin (2*m) → ℝ)) (μ : Measure (Fin (2*m) → ℝ)),
        IsFiniteMeasureOnCompacts μ → IsCompact K →
        ∀ psi : (Fin (2*m) → ℝ) → Config (2*m+1), Continuous psi →
        ∀ Tmap : Config (2*m+1) → ℂ,
        (∀ x∈K, absoluteEnergy (psi x)<σ ∧ ‖Tmap (psi x)‖≤r/2 ∧
          poleEquation B phi hphi 0 (Tmap (psi x)) (psi x)=0 ∧ AnalyticAt ℂ Tmap (psi x)) →
        let F := fun t => ∫ x in K,
          actualInnerRemainder B rootB phi hphi R₀ m (psi x) (Tmap (psi x)) t ∂μ
        AnalyticOnNhd ℂ F (ball 0 (c/(2*m+1:ℕ))) ∧
        (∀ j : ℕ, ‖iteratedDeriv j F 0/(j.factorial:ℂ)‖≤
          ((μ K).toReal*(C*remainderGaussianEnvelope M m))/((c/(2*m+1:ℕ))/2)^j) ∧
        (∀ j : ℕ, iteratedDeriv j F 0=∫ x in K,
          iteratedDeriv j (actualInnerRemainder B rootB phi hphi R₀ m
            (psi x) (Tmap (psi x))) 0 ∂μ) ∧
        (∀ x∈K, ∀ t∈ball 0 (c/(2*m+1:ℕ)), t≠Tmap (psi x) →
          formFactorNumerator B rootB phi hphi 0 t (psi x)*
            cothHalf (fun u => poleEquation B phi hphi 0 u (psi x)) t=
          (-2*formFactorNumerator B rootB phi hphi 0 (Tmap (psi x)) (psi x)/
            poleParameterDerivative B phi hphi 0 (Tmap (psi x)) (psi x))/(Tmap (psi x)-t)+
          actualInnerRemainder B rootB phi hphi R₀ m (psi x) (Tmap (psi x)) t) ∧
        (∀ t∈ball 0 (c/(2*m+1:ℕ)), IntegrableOn
          (fun x => actualInnerRemainder B rootB phi hphi R₀ m (psi x) (Tmap (psi x)) t) K μ) := by
  obtain ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,hs⟩ :=
    exists_actual_inner_remainder B rootB phi hphi hB hB0 hrB
  refine ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,?_⟩
  intro m K μ hμ hK psi hpsi Tmap hdata
  let _ := hμ
  let G : ℂ × Config (2*m+1) → ℂ := fun p =>
    actualInnerRemainder B rootB phi hphi R₀ m p.2 (Tmap p.2) p.1
  have ha : ∀ t∈ball (0:ℂ) (c/(2*m+1:ℕ)), ∀ x∈K, AnalyticAt ℂ G (t,psi x) := by
    intro t ht x hx
    have hd := hdata x hx
    have hh := (hs m (psi x) hd.1 (Tmap (psi x)) hd.2.1 hd.2.2.1).2.2.1
      Tmap hd.2.2.2 rfl t ht
    exact hh.fun_comp_of_eq (f := fun p : ℂ × Config (2*m+1) => (p.2,p.1))
      (analyticAt_snd.prod analyticAt_fst) rfl
  have hb : ∀ t∈ball (0:ℂ) (c/(2*m+1:ℕ)), ∀ x∈K, ‖G (t,psi x)‖≤C*remainderGaussianEnvelope M m := by
    intro t ht x hx
    have hd := hdata x hx
    exact (hs m (psi x) hd.1 (Tmap (psi x)) hd.2.1 hd.2.2.1).2.1 t ht
  have hh := compact_remainder_analytic_jets (μ := μ) hK G psi hpsi (by positivity) ha hb
  refine ⟨hh.1,hh.2.1,hh.2.2,?_,?_⟩
  · intro x hx t ht htT
    have hd := hdata x hx
    rw [(hs m (psi x) hd.1 (Tmap (psi x)) hd.2.1 hd.2.2.1).2.2.2 t ht htT]
    congr 1
    rw [show Tmap (psi x)-t=-(t-Tmap (psi x)) by ring,div_neg]
    ring
  · intro t ht
    have hc : ContinuousOn (fun x => G (t,psi x)) K := by
      intro x hx
      exact ((ha t ht x hx).continuousAt.comp
        (f := fun y => (t,psi y)) (continuous_const.prodMk hpsi).continuousAt).continuousWithinAt
    exact hc.integrableOn_compact (μ := μ) hK

end
end IsingBulk.Anisotropic.NegativeCycles
