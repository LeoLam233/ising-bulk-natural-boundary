import IsingBulk.HT22.Geometry.ActualAngularFieldBound
import IsingBulk.Preferred22.RightShellMeasure
import IsingBulk.Preferred22.CoordinateDiameter

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Metric IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators

/-- Actual whole-right angular field bound for puncturing the sole full
collision locus. The universal cap is chosen before the smooth bump. -/
theorem actual_angular_field_right_bound_full (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ C ε₀ τ₀ δB : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,-δB≤θ i+d.b ∧ θ i≤B.delta) →
      0<preferredAngularDiameter θ → ∀ a : Fin N,
      ‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ a‖≤
        C*(N:ℝ)^2/preferredAngularDiameter θ := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_angular_field_shell_bound_full d
    (10*Real.pi+10) (by positivity)
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨C,e,t,δ,hC,he,ht,hδ,hδB,hbound⟩ := hsource B hB
  refine ⟨C,min e 1,t,δ,hC,lt_min he zero_lt_one,ht,hδ,hδB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hD a
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ θ hne
  obtain ⟨k,_,hmax⟩ := Finset.exists_max_image Finset.univ θ hne
  have hext (j : Fin N) : θ i≤θ j ∧ θ j≤θ k :=
    ⟨hmin j (Finset.mem_univ _),hmax j (Finset.mem_univ _)⟩
  have hgap : preferredAngularDiameter θ≤θ k-θ i := by
    apply Metric.diam_le_of_forall_dist_le (sub_nonneg.mpr (hext k).1)
    rintro _ ⟨j,rfl⟩ _ ⟨q,rfl⟩
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [(hext j).1,(hext j).2,(hext q).1,(hext q).2]
  have hwin (j : Fin N) : θ i+d.b-2*preferredAngularDiameter θ≤θ j+d.b ∧
      θ j+d.b≤θ i+d.b+2*preferredAngularDiameter θ := by
    have hh := abs_le.mp (preferredAngularDiameter_pair_le θ j i)
    constructor <;> linarith [hh.1,hh.2]
  have hangle (j : Fin N) : θ j∈Ioc (-Real.pi) Real.pi :=
    preferred_right_interval_original d B hδB ⟨by linarith [(hθ j).1],(hθ j).2⟩
  have hDπ : preferredAngularDiameter θ≤2*Real.pi := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨j,rfl⟩ _ ⟨q,rfl⟩
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [(hangle j).1,(hangle j).2,(hangle q).1,(hangle q).2]
  have hμ : |θ i+d.b|≤2*Real.pi := by
    apply abs_le.mpr
    constructor <;> linarith [(hangle i).1,(hangle i).2,d.b_pos,d.b_lt]
  have hε1 : ε<1 := hεr.trans_le (min_le_right _ _)
  exact hbound N hN ε τ (θ i+d.b) (preferredAngularDiameter θ) hε
    (hεr.trans_le (min_le_left _ _)) hτ hτr hD (by linarith [Real.pi_pos])
    θ hθ hwin i k hext hgap a

end
end IsingBulk.HT22.Geometry
