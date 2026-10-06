import IsingBulk.Tail.CompactPhaseRegularity
import IsingBulk.Tail.SymmetricDiagonalDerivative
import IsingBulk.Tail.CompactSmoothDivision

/-! The actual complex freezing determinant and smooth division by a selected
angular difference. Only real smoothness is used for the coupled bumps. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def angularPairDeterminant {N : ℕ} (F G : (Fin N → ℝ) → ℂ) (i j : Fin N)
    (x : Fin N → ℝ) : ℂ :=
  fderiv ℝ F x (Pi.single i 1)*fderiv ℝ G x (Pi.single j 1)-
  fderiv ℝ F x (Pi.single j 1)*fderiv ℝ G x (Pi.single i 1)

theorem angularPairDeterminant_smooth {N : ℕ} {F G : (Fin N → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i j : Fin N) :
    ContDiff ℝ ∞ (angularPairDeterminant F G i j) := by
  exact (((hF.fderiv_right (by simp)).clm_apply contDiff_const).mul
    ((hG.fderiv_right (by simp)).clm_apply contDiff_const)).sub
    (((hF.fderiv_right (by simp)).clm_apply contDiff_const).mul
      ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

theorem angularPairDeterminant_diagonal {N : ℕ} (F G : (Fin N → ℝ) → ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFs : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (hGs : ∀ sigma : Equiv.Perm (Fin N), ∀ x, G (fun k => x (sigma k))=G x)
    (x : Fin N → ℝ) (i j : Fin N) (hij : x i=x j) : angularPairDeterminant F G i j x=0 := by
  unfold angularPairDeterminant
  rw [symmetric_coordinate_derivatives_equal F hFs x (hF.differentiable (by simp) x) i j hij,
    symmetric_coordinate_derivatives_equal G hGs x (hG.differentiable (by simp) x) i j hij,sub_self]

def pairInsertion {N : ℕ} (i j : Fin N) (z : (ℝ × ℝ) × (Fin N → ℝ)) : Fin N → ℝ :=
  fun l => if l=i then z.1.1 else if l=j then z.1.2 else z.2 l

theorem pairInsertion_smooth {N : ℕ} (i j : Fin N) : ContDiff ℝ ∞ (pairInsertion i j) := by
  apply contDiff_pi.mpr
  intro l
  by_cases hli : l=i
  · simpa [pairInsertion,hli] using (contDiff_fst.fst : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin N → ℝ) => z.1.1))
  · by_cases hlj : l=j
    · have hji : j≠i := by simpa only [hlj] using hli
      simpa [pairInsertion,hlj,hji] using (contDiff_fst.snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin N → ℝ) => z.1.2))
    · simpa [pairInsertion,hli,hlj,Function.comp_def] using (contDiff_apply ℝ ℝ l).comp
        (contDiff_snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin N → ℝ) => z.2))

theorem pairInsertion_recover {N : ℕ} (i j : Fin N) (x : Fin N → ℝ) :
    pairInsertion i j ((x i,x j),x)=x := by
  funext l
  by_cases hli : l=i
  · subst l; simp [pairInsertion]
  · by_cases hlj : l=j
    · subst l; simp [pairInsertion,hli]
    · simp [pairInsertion,hli,hlj]

def angularPairDividedDifference {N : ℕ} (F G : (Fin N → ℝ) → ℂ) (i j : Fin N)
    (x : Fin N → ℝ) : ℂ :=
  smoothDividedDifference (fun z => angularPairDeterminant F G i j (pairInsertion i j z))
    ((x i,x j),x)

theorem angularPairDividedDifference_smooth {N : ℕ} {F G : (Fin N → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i j : Fin N) :
    ContDiff ℝ ∞ (angularPairDividedDifference F G i j) := by
  exact (smoothDividedDifference_contDiff _ ((angularPairDeterminant_smooth hF hG i j).comp
    (pairInsertion_smooth i j))).comp
    (((contDiff_apply ℝ ℝ i).prodMk (contDiff_apply ℝ ℝ j)).prodMk contDiff_id)

theorem angularPairDividedDifference_identity {N : ℕ} (F G : (Fin N → ℝ) → ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFs : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (hGs : ∀ sigma : Equiv.Perm (Fin N), ∀ x, G (fun k => x (sigma k))=G x)
    (i j : Fin N) (x : Fin N → ℝ) :
    angularPairDeterminant F G i j x=(x i-x j : ℝ) • angularPairDividedDifference F G i j x := by
  have hh := smoothDividedDifference_identity
    (fun z => angularPairDeterminant F G i j (pairInsertion i j z))
    ((angularPairDeterminant_smooth hF hG i j).comp (pairInsertion_smooth i j)) ((x i,x j),x)
  have hdiag : angularPairDeterminant F G i j (pairInsertion i j ((x j,x j),x))=0 := by
    apply angularPairDeterminant_diagonal F G hF hG hFs hGs
    by_cases hij : i=j
    · subst j; rfl
    · simp [pairInsertion,Ne.symm hij]
  simpa only [pairInsertion_recover,hdiag,sub_zero,angularPairDividedDifference] using hh

def currentAngularDeterminant {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (i j : Fin N) : (Fin N → ℝ) → ℂ :=
  angularPairDeterminant (unwrappedLogY f r τ lam) (currentComplexPhase f r τ lam s) i j

def currentAngularDividedDifference {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (i j : Fin N) : (Fin N → ℝ) → ℂ :=
  angularPairDividedDifference (unwrappedLogY f r τ lam) (currentComplexPhase f r τ lam s) i j

/-- Literal actual-source division on the original sheet. The coefficient is
an explicit transverse derivative integral, with no analytic bump extension. -/
theorem currentAngularDeterminant_smooth_division {N : ℕ} (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) (i j : Fin N) :
    ContDiff ℝ ∞ (currentAngularDividedDifference (N := N) f r τ lam s i j) ∧
      ∀ x, currentAngularDeterminant f r τ lam s i j x=
        (x i-x j : ℝ) • currentAngularDividedDifference f r τ lam s i j x := by
  have hF := unwrappedLogY_contDiff (N := N) f r τ lam hf.p_smooth hf.m_smooth
  have hG := currentComplexPhase_contDiff hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth
    hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmargin
  exact ⟨angularPairDividedDifference_smooth hF hG i j,
    angularPairDividedDifference_identity _ _ hF hG
      (fun sigma x => unwrappedLogY_equiv f r τ lam x sigma)
      (fun sigma x => currentComplexPhase_equiv f r τ lam s x sigma) i j⟩

end
end IsingBulk.Tail
