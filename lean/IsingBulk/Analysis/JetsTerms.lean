import IsingBulk.Analysis.JetsMultiindex
import IsingBulk.Analysis.JetsPoleRecurrence
import IsingBulk.Analysis.JetDescriptors

/-! Source-form terms with genuine derivative words and an explicit regular
numerator for the selected pole. The recursive list is only identified with
analytic operations by separate realization theorems. -/
namespace IsingBulk.Jets
noncomputable section

structure SourceJetTerm (N : ℕ) where
  pole : ℕ
  cutoff : List (Fin N)
  numerator : List (Option (Fin N))
  regularPart : ℂ × (Fin N → ℂ) → ℂ

def SourceJetTerm.descriptor {N : ℕ} (T : SourceJetTerm N) : JetDescriptor :=
  ⟨T.pole,T.cutoff.length,parameterOrder T.numerator,(spatialWord T.numerator).length⟩

def SourceJetTerm.coefficient {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (z : ℂ × (Fin N → ℂ)) : ℂ := T.regularPart z/(selectedDifferenceCLM p q z)^T.pole

def SourceJetTerm.density {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (Q : ℂ × (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  T.coefficient p q (s,φ) * numeratorJet T.numerator Q (s,φ) / regularKernel s φ

def SourceJetTerm.value {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (Q : ℂ × (Fin N → ℂ) → ℂ)
    (x : Fin N → ℝ) (z : ℂ × (Fin N → ℂ)) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ) * T.density p q Q z.1 z.2

def SourceJetTerm.child {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (a : JetAction N) : SourceJetTerm N :=
  match a with
  | .coefficientParameter => {T with regularPart := fun z => fderiv ℂ T.regularPart z (1,0)}
  | .coefficientSpatial i => {T with
      pole := T.pole+2
      regularPart := fun z => residualRegularNumerator p q i z.1 z.2 *
        poleJetNumerator T.pole T.regularPart (selectedDifferenceCLM p q) (spatialDirection i) z}
  | .divergence => {T with
      pole := T.pole+2
      regularPart := fun z => divergenceRegularNumerator p q z * T.regularPart z}
  | .numeratorSpatial i => {T with
      pole := T.pole+1
      numerator := some i::T.numerator
      regularPart := fun z => residualRegularNumerator p q i z.1 z.2 * T.regularPart z}
  | .numeratorParameter => {T with numerator := none::T.numerator}
  | .cutoffSpatial i => {T with
      pole := T.pole+1
      cutoff := i::T.cutoff
      regularPart := fun z => -fieldRegularNumerator p q i z.1 z.2 * T.regularPart z}

theorem SourceJetTerm.child_descriptor {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (a : JetAction N) : (T.child p q a).descriptor = a.apply T.descriptor := by
  cases a <;> rfl

def sourceJetTerms {N : ℕ} (p q : Fin N) : ℕ → List (SourceJetTerm N)
  | 0 => [⟨0,[],[],fun _ => 1⟩]
  | j+1 => (sourceJetTerms p q j).flatMap (fun T => (actions N).map (T.child p q))

theorem sourceJetTerms_descriptors {N : ℕ} (p q : Fin N) (j : ℕ) :
    (sourceJetTerms p q j).map SourceJetTerm.descriptor = descendants N j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [sourceJetTerms, List.map_flatMap, List.map_map, descendants, Function.comp_def]
    simp_rw [SourceJetTerm.child_descriptor]
    rw [← ih, List.flatMap_map]

theorem sourceJetTerms_valid {N : ℕ} (p q : Fin N) (j : ℕ)
    (T : SourceJetTerm N) (hT : T ∈ sourceJetTerms p q j) :
    T.pole+T.cutoff.length+(spatialWord T.numerator).length ≤ 2*j ∧
      parameterOrder T.numerator+T.cutoff.length+(spatialWord T.numerator).length ≤ j := by
  apply descendants_valid N j T.descriptor
  rw [← sourceJetTerms_descriptors p q j]
  exact List.mem_map.mpr ⟨T,hT,rfl⟩

theorem sourceJetTerms_length {N : ℕ} (p q : Fin N) (j : ℕ) :
    (sourceJetTerms p q j).length = (3+3*N)^j := by
  have hh := congrArg List.length (sourceJetTerms_descriptors p q j)
  simpa only [List.length_map, descendants_length] using hh

/-- This controls the actual term list. Identification of its sum with the
iterated source operation is a separate analytic obligation. -/
theorem sourceJetTerms_source_bound (j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ p q : Fin N,
      (sourceJetTerms p q j).length ≤ C*N^C := by
  obtain ⟨C,hC,h⟩ := descendants_source_bound j
  refine ⟨C,hC,fun N hN p q => ?_⟩
  simpa only [sourceJetTerms_length, descendants_length] using h N hN

theorem SourceJetTerm.child_analytic {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (a : JetAction N) (z : ℂ × (Fin N → ℂ))
    (hT : AnalyticAt ℂ T.regularPart z)
    (hV : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) z)
    (hB : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z) :
    AnalyticAt ℂ (T.child p q a).regularPart z := by
  have hdiv : AnalyticAt ℂ (divergenceRegularNumerator p q) z :=
    Finset.analyticAt_fun_sum _ fun i _ => poleDerivativeNumerator_analytic _ _ z _ (hB i)
  cases a with
  | coefficientParameter =>
    exact ((ContinuousLinearMap.apply ℂ ℂ (1,0)).analyticAt _).comp hT.fderiv
  | coefficientSpatial i =>
    exact (hB i).mul (poleJetNumerator_analytic T.pole T.regularPart _ z _ hT)
  | divergence => exact hdiv.mul hT
  | numeratorSpatial i => exact (hB i).mul hT
  | numeratorParameter => exact hT
  | cutoffSpatial i => exact (hV i).neg.mul hT

theorem sourceJetTerms_analytic {N : ℕ} (p q : Fin N) (j : ℕ)
    (z : ℂ × (Fin N → ℂ))
    (hV : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) z)
    (hB : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z) :
    ∀ T ∈ sourceJetTerms p q j, AnalyticAt ℂ T.regularPart z := by
  induction j with
  | zero => simpa [sourceJetTerms] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × (Fin N → ℂ) => (1:ℂ)) z)
  | succ j ih =>
    intro T hT
    obtain ⟨S,hS,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    exact S.child_analytic p q a z (ih S hS) hV hB

/-- The regular coefficient germs in the recursively generated list are
constructed from the actual source formulas, including at the diagonal. -/
theorem sourceJetTerms_analytic_base {N : ℕ} (p q : Fin N) (j : ℕ)
    (s : ℂ) (c : ℝ) (hs : s ≠ 0) (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    ∀ T ∈ sourceJetTerms p q j, AnalyticAt ℂ T.regularPart (s,0) :=
  sourceJetTerms_analytic p q j (s,0)
    (fun i => (field_numerators_analytic p q i s c hs hS hc).1)
    (fun i => (field_numerators_analytic p q i s c hs hS hc).2)

theorem SourceJetTerm.cleared_coefficient {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (z : ℂ × (Fin N → ℂ)) (hd : z.2 q-z.2 p ≠ 0) :
    (z.2 q-z.2 p)^T.pole*T.coefficient p q z = T.regularPart z := by
  have hd' : selectedDifferenceCLM p q z ≠ 0 := hd
  change (selectedDifferenceCLM p q z)^T.pole*
    (T.regularPart z/(selectedDifferenceCLM p q z)^T.pole) = T.regularPart z
  field_simp [hd']

/-- Source-form interpretation of the numerator word for every term.
The numerator remains Delta squared times the regular factor. -/
theorem SourceJetTerm.unfactored_density {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (A : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ))
    (hA : AnalyticAt ℂ A z) :
    T.density p q (unfactoredNumerator A) z.1 z.2 =
      T.coefficient p q z * numeratorJet
        (List.replicate (parameterOrder T.numerator) none ++ (spatialWord T.numerator).map some)
        (unfactoredNumerator A) z / regularKernel z.1 z.2 := by
  unfold SourceJetTerm.density
  rw [numeratorJet_canonical T.numerator _ z (unfactoredNumerator_analytic A z hA)]

end
end IsingBulk.Jets
