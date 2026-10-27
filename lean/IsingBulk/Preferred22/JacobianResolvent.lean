import IsingBulk.Preferred22.ExtremeFiberIntegration
import IsingBulk.Preferred22.OneBodyScale

/-! The literal physical Jacobian/resolvent majorant in source q20 and its
actual fixed-fiber one-body reduction. No transported-density estimate is
assumed in the declarations of this module. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

def preferredJacobianResolvent {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∏ i, ‖actualBumpSlopeVector d B ε τ θ i+1‖)/‖1-preferredActualZ d B ε τ θ‖

theorem preferredJacobianResolvent_nonneg {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) :
    0 ≤ preferredJacobianResolvent d B ε τ θ := by
  unfold preferredJacobianResolvent
  positivity

theorem occupancy_equiv {N : ℕ} (p : ℝ → ℝ) (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    occupancy p (θ ∘ e)=occupancy p θ := by
  exact Equiv.sum_comp e (fun i => p (θ i))

theorem deformedAngles_equiv {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (i : Fin N) :
    deformedAngles τ p m (θ ∘ e) i=deformedAngles τ p m θ (e i) := by
  simp only [deformedAngles,balancedShift,occupancy_equiv,Function.comp_apply]

theorem actualBumpSlopeVector_equiv {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ)
    (e : Equiv.Perm (Fin N)) (i : Fin N) :
    actualBumpSlopeVector d B ε τ (θ ∘ e) i=actualBumpSlopeVector d B ε τ θ (e i) := by
  simp only [actualBumpSlopeVector,occupancy_equiv,Function.comp_apply]

theorem preferredActualZ_equiv {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    preferredActualZ d B ε τ (θ ∘ e)=preferredActualZ d B ε τ θ := by
  unfold preferredActualZ
  simp only [deformedAngles_equiv]
  exact Equiv.prod_comp e (fun i : Fin N =>
    physicalRoot (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)))

theorem preferredJacobianResolvent_equiv {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    preferredJacobianResolvent d B ε τ (θ ∘ e)=preferredJacobianResolvent d B ε τ θ := by
  unfold preferredJacobianResolvent
  rw [preferredActualZ_equiv]
  simp only [actualBumpSlopeVector_equiv]
  rw [Equiv.prod_comp e (fun i : Fin N => ‖actualBumpSlopeVector d B ε τ θ i+1‖)]

/-- Actual one-body reduction of all non-extreme Jacobian factors. The two
extreme factors stay together with the complete product denominator. -/
theorem preferred_geometric_fiber_jacobian_bound (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      δB ≤ δ₀ → ∀ z : Fin n → ℝ, ∀ m : ℝ,
      m ∈ extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z →
      preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z m) ≤
        A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b)) *
          (preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
            ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖) := by
  obtain ⟨A,_,ε₀,τ₀,δ₀,hA,_,hε₀,hτ₀,hδ₀,hδ₀δ,_,_,_,hsource⟩ :=
    preferred_full_right_onebody_and_attenuation d B
  refine ⟨A,ε₀,τ₀,δ₀,hA,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n ε τ c r δB hε hεr hτ hτr hδ z m hm
  let θ := preferredFiberConfiguration c z m
  let σ := occupancy B.p θ/((n+2:ℕ):ℝ)
  let υ := occupancy B.m θ/((n+2:ℕ):ℝ)
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box (by omega : 0 < n+2) B θ
  have hg := (preferredFiberConfiguration_geometry hm).1
  have hbody (a : Fin n) :
      ‖actualBumpSlopeVector d B ε τ θ a.succ.castSucc+1‖ ≤
        A*preferredOneBodyMajorant ε (z a+d.b) := by
    have hθa := hg a.succ.castSucc
    rw [preferredFiberConfiguration_other] at hθa
    have huL : -δ₀ ≤ z a+d.b := by linarith [hθa.1]
    have huR : z a+d.b ≤ d.b+B.delta := by linarith [hθa.2]
    have hh := (hsource ε τ σ υ (z a+d.b) hε hεr hτ hτr hσ hυ huL huR).1
    rw [show -d.b+(z a+d.b)=z a by ring] at hh
    calc
      _ ≤ A/Real.sqrt (|z a+d.b|+ε) := by
        change ‖preferredCompactSlope d B.m B.p ε τ σ υ
          (preferredFiberConfiguration c z m a.succ.castSucc)+1‖ ≤ _
        rw [preferredFiberConfiguration_other]
        exact hh
      _ = _ := by unfold preferredOneBodyMajorant; ring
  let f := fun i : Fin (n+2) => ‖actualBumpSlopeVector d B ε τ θ i+1‖
  have hp : (∏ a : Fin n, f a.succ.castSucc) ≤ A^n*(∏ a : Fin n,preferredOneBodyMajorant ε (z a+d.b)) := by
    have hh := Finset.prod_le_prod₀ (fun (a : Fin n) (_ : a ∈ Finset.univ) => norm_nonneg
      (actualBumpSlopeVector d B ε τ θ a.succ.castSucc+1)) (fun a _ => hbody a)
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  have hprod : (∏ i : Fin (n+2),f i)=(f 0*f (Fin.last (n+1)))*(∏ a : Fin n,f a.succ.castSucc) := by
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero]
    ring
  have hpair : preferredExtremePair d B ε τ θ 0 (Fin.last (n+1))=f 0*f (Fin.last (n+1)) := by
    exact norm_mul _ _
  change (∏ i,f i)/_ ≤ _
  rw [hprod,← hpair]
  calc
    _ ≤ (preferredExtremePair d B ε τ θ 0 (Fin.last (n+1)) *
        (A^n*(∏ a : Fin n,preferredOneBodyMajorant ε (z a+d.b))))/
          ‖1-preferredActualZ d B ε τ θ‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by unfold preferredExtremePair; positivity)) (norm_nonneg _)
    _ = _ := by ring

end
end IsingBulk.Preferred22
