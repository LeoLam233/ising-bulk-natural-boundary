import IsingBulk.First.ResidueRegularity
import Mathlib.MeasureTheory.Integral.TorusIntegral

/-! Fubini bridge for the full coupled angular integrand; no separable-product
formula is substituted for the actual Ising density. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

 theorem setIntegral_prod_reverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (f : A × B → ℂ) (s : Set A) (t : Set B)
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    (∫ p in s ×ˢ t, f p ∂μ.prod ν) = ∫ y in t, ∫ x in s, f (x,y) ∂μ ∂ν := by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod_symm f hf

theorem angleBox_integral_succ (n : ℕ) (f : (Fin (n+1) → ℝ) → ℂ) (hf : Continuous f) :
    (∫ θ in angleBox (n+1), f θ) = ∫ θ in angleBox n,
      ∫ u : ℝ in 0..2*Real.pi, f (Fin.cons u θ) := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ), e p = Fin.cons p.1 p.2 := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv ]
  have hbox : e ⁻¹' angleBox (n+1) = Icc (0:ℝ) (2*Real.pi) ×ˢ angleBox n := by
    ext p
    simp only [mem_preimage, he, angleBox, mem_Icc, mem_prod]
    constructor
    · intro hp
      exact ⟨⟨hp.1 0, hp.2 0⟩, ⟨fun i => hp.1 i.succ, fun i => hp.2 i.succ⟩⟩
    · intro hp
      constructor <;> intro i
      · exact Fin.cases hp.1.1 (fun j => hp.2.1 j) i
      · exact Fin.cases hp.1.2 (fun j => hp.2.2 j) i
  have hcomp : Continuous (fun p : ℝ × (Fin n → ℝ) => f (e p)) := by
    simp only [he]
    exact hf.comp (by fun_prop)
  have hi : IntegrableOn (fun p => f (e p)) (Icc (0:ℝ) (2*Real.pi) ×ˢ angleBox n)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hcomp.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← hem.map_eq, setIntegral_map_equiv, hbox, Measure.volume_eq_prod,
    setIntegral_prod_reverse volume volume _ _ _ hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  dsimp only
  rw [he]

theorem multiAngleIntegral_eq_box (N : ℕ) (f : (Fin N → ℝ) → ℂ) (hf : Continuous f) :
    multiAngleIntegral N f = ∫ θ in angleBox N, f θ := by
  classical
  induction N with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (Fin.elim0 : Fin 0 → ℝ)]
    rw [setIntegral_dirac]
    simp only [multiAngleIntegral]
    have he : (Fin.elim0 : Fin 0 → ℝ) ∈ angleBox 0 := by
      constructor <;> intro i <;> exact Fin.elim0 i
    simp [he]
  | succ n ih =>
    rw [multiAngleIntegral, angleBox_integral_succ n f hf]
    apply ih
    apply continuous_angle_integral
    exact hf.comp (by fun_prop)

end
end IsingBulk.First
