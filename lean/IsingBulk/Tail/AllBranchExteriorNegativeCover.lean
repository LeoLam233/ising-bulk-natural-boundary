import IsingBulk.Tail.AllBranchExteriorNegativeIntegral
import IsingBulk.Tail.FiniteIntegralCover

/-! Cover the negative region by the sign of the named anchor. A negative
anchor supplies its own gap; a positive anchor is distinct from every chosen
negative coordinate. No auxiliary negative cutoff scale is needed. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Lie Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 800000

def allBranchExteriorNegativeRegion {N : ℕ} (p : Fin N) (R a : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => -R) (fun _ => R) ∩ {u | a ≤ |u p| ∧ ∃ v, u v ≤ 0}

def allBranchExteriorNegativeCost {d : LocalBranchData} (B : BranchEstimates d)
    (ε R a c C : ℝ) (N : ℕ) : ℝ :=
  (2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt a))*
    (((N:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*B.lengthC^(N-1))+
  (N:ℝ)*((2*(B.magnitudeUpper/Real.sqrt a)*C)*
    (((N:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*(2*Real.log ((R+ε)/ε))*B.lengthC^(N-2)))

theorem allBranchExterior_negative_region_integral {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ ε R a : ℝ,
      0 < ε → ε ≤ B.ε₀ → 0 ≤ R → R ≤ B.r → R ≤ Real.pi → d.c₀*ε ≤ 1 → 0 < a →
      (∀ u : AngularSpace n, u ∈ Icc (fun _ => -R) (fun _ => R) →
        MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) →
      ∀ p q : Fin (n+1), p ≠ q →
      IntegrableOn (allBranchExteriorKernelDensity d ε) (allBranchExteriorNegativeRegion p R a) ∧
      (∫ u in allBranchExteriorNegativeRegion p R a, allBranchExteriorKernelDensity d ε u) ≤
        allBranchExteriorNegativeCost B ε R a c C (n+1) := by
  classical
  obtain ⟨c,C,hc,hC,hint⟩ := allBranchExterior_negative_integral_bounds B
  refine ⟨c,C,hc,hC,?_⟩
  intro n ε R a hε hεr hR hRB hRπ hα1 ha hchart p q hpq
  let box := Icc (fun _ : Fin (n+1) => -R) (fun _ => R)
  let S := allBranchExteriorNegativeRegion p R a
  let K := @allBranchExteriorKernelDensity (n+1) d ε
  let cell : Option (Fin (n+1)) → Set (AngularSpace n)
    | none => box ∩ {u | u p ≤ -a}
    | some v => if v=p then ∅ else box ∩ {u | a ≤ u p ∧ u v ≤ 0}
  let A := (2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt a))*
    (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*B.lengthC^((n+1)-1))
  let D := (2*(B.magnitudeUpper/Real.sqrt a)*C)*
    (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*(2*Real.log ((R+ε)/ε))*B.lengthC^((n+1)-2))
  have hS : MeasurableSet S := by unfold S allBranchExteriorNegativeRegion; measurability
  have hcell : ∀ i, MeasurableSet (cell i) := by
    intro i
    cases i with
    | none => dsimp [cell,box]; measurability
    | some v => dsimp [cell,box]; split_ifs <;> measurability
  have hsub : ∀ i, cell i ⊆ box := by
    intro i u hu
    cases i with
    | none => exact hu.1
    | some v =>
      dsimp [cell] at hu
      split_ifs at hu
      · exact False.elim hu
      · exact hu.1
  have hKi : IntegrableOn K box :=
    (allBranchExterior_kernel_density_continuousOn d hε box hchart).integrableOn_compact isCompact_Icc
  have hKS : IntegrableOn K S := hKi.mono_set (fun _ hu => hu.1)
  have hlog : 0 ≤ Real.log ((R+ε)/ε) := Real.log_nonneg ((one_le_div hε).mpr (by linarith))
  have hD : 0 ≤ D := by
    have hmag := B.magnitudeUpper_pos
    have hlen := B.lengthC_pos
    have hkernel := simpleKernelConstant_pos
    dsimp [D]
    positivity
  have hbounds (i : Option (Fin (n+1))) : (∫ u in cell i, K u) ≤ (match i with | none => A | some _ => D) := by
    cases i with
    | none =>
      have hgeom (u : AngularSpace n) (hu : u ∈ cell none) : a ≤ |u p| ∧ u p ≤ 0 := by
        have hh : u p ≤ -a := hu.2
        have hn : u p ≤ 0 := by linarith
        rw [abs_of_nonpos hn]
        exact ⟨by linarith,hn⟩
      exact (hint n ε R a hε hεr hR hRB hRπ hα1 ha hchart p q p hpq (cell none)
        (hcell none) (hsub none) hgeom).2.2 a ha (fun u hu => (hgeom u hu).1)
    | some v =>
      by_cases hvp : v=p
      · simp only [cell,hvp,ite_true,setIntegral_empty]
        exact hD
      · have hgeom (u : AngularSpace n) (hu : u ∈ cell (some v)) : a ≤ |u p| ∧ u v ≤ 0 := by
          have hh : u ∈ box ∩ {u | a ≤ u p ∧ u v ≤ 0} := by simpa only [cell,hvp,ite_false] using hu
          exact ⟨hh.2.1.trans (le_abs_self _),hh.2.2⟩
        exact (hint n ε R a hε hεr hR hRB hRπ hα1 ha hchart p q v hpq (cell (some v))
          (hcell (some v)) (hsub (some v)) hgeom).2.1 (Ne.symm hvp)
  have hcover (u : AngularSpace n) (hu : u ∈ S) : ∃ i, u ∈ cell i := by
    obtain ⟨v,hv⟩ := hu.2.2
    by_cases hp : u p ≤ 0
    · refine ⟨none,hu.1,?_⟩
      have hh := hu.2.1
      rw [abs_of_nonpos hp] at hh
      change u p ≤ -a
      linarith
    · have hp' : 0 < u p := lt_of_not_ge hp
      have hvp : v ≠ p := by intro he; subst v; linarith
      refine ⟨some v,?_⟩
      simp only [cell,hvp,ite_false]
      exact ⟨hu.1,by simpa only [abs_of_pos hp'] using hu.2.1,hv⟩
  refine ⟨hKS,?_⟩
  calc
    _ ≤ ∑ i, ∫ u in cell i, K u := setIntegral_le_finite_cover hS hKS
      (allBranchExterior_kernel_density_nonneg d ε) cell hcell (fun i => hKi.mono_set (hsub i)) hcover
    _ ≤ ∑ i : Option (Fin (n+1)), (match i with | none => A | some _ => D) :=
      Finset.sum_le_sum (fun i _ => hbounds i)
    _ = _ := by simp [Fintype.sum_option,allBranchExteriorNegativeCost,A,D,Nat.cast_add,Nat.cast_one]

end
end IsingBulk.Tail
