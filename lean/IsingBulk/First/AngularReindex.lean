import IsingBulk.First.LocalizedAnalytic
import IsingBulk.First.CompatibleComplement

/-! Equality transport for the actual finite angular domains. These helpers
resolve the source N=n+1 indexing without changing measures or densities. -/
namespace IsingBulk.First
noncomputable section
open Set
open scoped ContDiff

def reindexYWeight {M N : ℕ} (h : M=N) (w : (Fin M → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  fun x => w (reindexAngles h x)

def reindexDoubleWeight {M N : ℕ} (h : M=N) (w : DoubleAngularVector M → ℝ) :
    DoubleAngularVector N → ℝ := fun p => w (reindexAngles h p.1,reindexAngles h p.2)

theorem reindexYWeight_smooth {M N : ℕ} (h : M=N) (w : (Fin M → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (reindexYWeight h w) := by
  cases h
  exact hw

theorem reindexDoubleWeight_smooth {M N : ℕ} (h : M=N) (w : DoubleAngularVector M → ℝ)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (reindexDoubleWeight h w) := by
  cases h
  exact hw

theorem reindexDoubleWeight_periodic {M N : ℕ} (h : M=N) (w : DoubleAngularVector M → ℝ)
    (hw : DoubleCoordinatePeriodic w) : DoubleCoordinatePeriodic (reindexDoubleWeight h w) := by
  cases h
  exact hw

theorem reindexYWeight_tsupport {M N : ℕ} (h : M=N) (w : (Fin M → ℝ) → ℝ)
    (x : Fin N → ℝ) : x ∈ tsupport (reindexYWeight h w) ↔ reindexAngles h x ∈ tsupport w := by
  cases h
  rfl

theorem reindexDoubleWeight_tsupport {M N : ℕ} (h : M=N) (w : DoubleAngularVector M → ℝ)
    (x : DoubleAngularVector N) : x ∈ tsupport (reindexDoubleWeight h w) ↔
      (reindexAngles h x.1,reindexAngles h x.2) ∈ tsupport w := by
  cases h
  rfl

theorem weightedReducedFormFactor_reindex {M N : ℕ} (h : M=N) (r : ℝ) (z : ℂ → ℂ)
    (w : (Fin M → ℝ) → ℝ) :
    weightedReducedFormFactor N r z (reindexYWeight h w) = weightedReducedFormFactor M r z w := by
  cases h
  rfl

theorem weightedDoubleFormFactor_reindex {M N : ℕ} (h : M=N) (r : ℝ) (s : ℂ)
    (w : (Fin M → ℝ) → ℝ) :
    weightedDoubleFormFactor N r s (reindexYWeight h w) = weightedDoubleFormFactor M r s w := by
  cases h
  rfl

theorem localizedDoubleFormFactor_reindex {M N : ℕ} (h : M=N) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector M → ℝ) :
    localizedDoubleFormFactor N r s (reindexDoubleWeight h w) = localizedDoubleFormFactor M r s w := by
  cases h
  rfl

theorem localizedDoubleFormFactor_iteratedDeriv_reindex {M N : ℕ} (h : M=N) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector M → ℝ) (j : ℕ) :
    iteratedDeriv j (fun z => localizedDoubleFormFactor N r z (reindexDoubleWeight h w)) s =
      iteratedDeriv j (fun z => localizedDoubleFormFactor M r z w) s := by
  cases h
  rfl

theorem localizedDoubleFormFactor_y_reindex {M N : ℕ} (h : M=N) (r : ℝ) (s : ℂ)
    (w : (Fin M → ℝ) → ℝ) :
    localizedDoubleFormFactor N r s (fun p => reindexYWeight h w p.2) =
      localizedDoubleFormFactor M r s (fun p => w p.2) := by
  cases h
  rfl

theorem localizedDoubleFormFactor_iteratedDeriv_y_reindex {M N : ℕ} (h : M=N)
    (r : ℝ) (s : ℂ) (w : (Fin M → ℝ) → ℝ) (j : ℕ) :
    iteratedDeriv j (fun z => localizedDoubleFormFactor N r z (fun p => reindexYWeight h w p.2)) s =
      iteratedDeriv j (fun z => localizedDoubleFormFactor M r z (fun p => w p.2)) s := by
  cases h
  rfl

theorem compatibleDoubleComplement_source_integral {n N : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U)
    (r : ℝ) (s : ℂ) :
    localizedDoubleFormFactor N r s (compatibleDoubleComplement h c) =
      localizedDoubleFormFactor (n+1) r s (fun p => c.remainder p.2) :=
  localizedDoubleFormFactor_y_reindex h r s c.remainder

/-- Direct attachment of the n+1 source split to the selected-N complement
bound, including the library's iterated-derivative notation conversion. -/
theorem compatibleDoubleComplement_source_derivative {n N : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (h : n+1=N) (c : CompatibleYCutoffData n alpha beta U)
    (r : ℝ) (s : ℂ) (j : ℕ) :
    iteratedDeriv j (fun z => localizedDoubleFormFactor (n+1) r z (fun p => c.remainder p.2)) s =
      (deriv^[j] (fun z => localizedDoubleFormFactor N r z (compatibleDoubleComplement h c))) s := by
  cases h
  rw [iteratedDeriv_eq_iterate]
  rfl

end
end IsingBulk.First
