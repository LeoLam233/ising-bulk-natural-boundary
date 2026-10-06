import IsingBulk.First.SelectedYCutoffs
import IsingBulk.First.DoublePeriodicBump

/-! The actually constructed y-only complement is smooth, periodic and
avoids both bad full configurations. Particle-index transport is explicit. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter
open scoped Topology ContDiff

def reindexAngles {N M : ℕ} (h : N=M) (u : Fin M → ℝ) : Fin N → ℝ :=
  fun i => u (Fin.cast h i)

theorem reindexAngles_contDiff {N M : ℕ} (h : N=M) : ContDiff ℝ ∞ (reindexAngles h) := by
  unfold reindexAngles
  fun_prop

def compatibleDoubleComplement {n N : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}
    (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U) (u : DoubleAngularVector N) : ℝ :=
  c.remainder (reindexAngles h u.2)

theorem compatibleDoubleComplement_contDiff {n N : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}
    (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U) :
    ContDiff ℝ ∞ (compatibleDoubleComplement h c) :=
  c.remainder_smooth.comp ((reindexAngles_contDiff h).comp contDiff_snd)

theorem compatibleDoubleComplement_periodic {n N : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}
    (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U) :
    DoubleCoordinatePeriodic (compatibleDoubleComplement h c) := by
  subst N
  intro u i
  constructor
  · rfl
  · change fixedYComplement alpha beta c.chi c.eta (Function.update u.2 i (u.2 i+2*Real.pi)) =
      fixedYComplement alpha beta c.chi c.eta u.2
    simp only [fixedYComplement,fixedYChartWeight_update_period]

theorem compatibleDoubleComplement_not_support {n N : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}
    (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U) {u : DoubleAngularVector N}
    (hy : (∀ j, exp ((u.2 j:ℂ)*I)=exp (-(alpha:ℂ)*I)) ∨
      (∀ j, exp ((u.2 j:ℂ)*I)=exp (-(beta:ℂ)*I))) :
    u ∉ tsupport (compatibleDoubleComplement h c) := by
  have hout : reindexAngles h u.2 ∉ tsupport c.remainder := by
    apply c.remainder_excludes_actual_y
    rcases hy with hl | hr
    · exact Or.inl (fun j => hl (Fin.cast h j))
    · exact Or.inr (fun j => hr (Fin.cast h j))
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hz := notMem_tsupport_iff_eventuallyEq.mp hout
  have hm : ContinuousAt (fun p : DoubleAngularVector N => reindexAngles h p.2) u :=
    ((reindexAngles_contDiff h).continuous.comp continuous_snd).continuousAt
  exact hz.comp_tendsto hm.tendsto

/-- No selected bad configuration lies in the actual complementary support;
all x angular variables remain unrestricted and unweighted. -/
theorem selected_compatible_complement_good {p : ℕ} (hp : p.Prime) {a b : ℤ}
    {U : Set (Fin (2*p-1) → ℝ)}
    (c : CompatibleYCutoffData (2*p-1) (PrimeFamily.angle p a) (PrimeFamily.angle p b) U) :
    let hN : 2*p-1+1=2*p := by have := hp.pos; omega
    ContDiff ℝ ∞ (compatibleDoubleComplement hN c) ∧
      DoubleCoordinatePeriodic (compatibleDoubleComplement hN c) ∧
      (∀ u ∈ tsupport (compatibleDoubleComplement hN c),
        ¬ selectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) := by
  dsimp only
  refine ⟨compatibleDoubleComplement_contDiff _ c,compatibleDoubleComplement_periodic _ c,?_⟩
  intro u hu hbad
  apply compatibleDoubleComplement_not_support (by have := hp.pos; omega) c (u := u) _ hu
  rcases hbad with h | h
  · right
    intro j
    have hh := h.2 j
    simpa [angleTuple,anglePoint,circleMap,selectedLowerRoot,mul_comm] using hh
  · left
    intro j
    have hh := h.2 j
    simpa [angleTuple,anglePoint,circleMap,selectedLowerRoot,mul_comm] using hh

end
end IsingBulk.First
