import IsingBulk.Analysis.LieIntegration

/-! Piecewise rectangular excisions of a periodic coordinate domain. Face
pairings are certified by positions and transverse rectangles, independently
of the integrated vector field. Unpaired faces lie on the removed region's
boundary. -/
namespace IsingBulk.Lie
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

abbrev BoxFace (n m : ℕ) := Fin m × Fin (n+1) × Bool

def faceHeight {n m : ℕ} (a b : Fin m → AngularSpace n) (f : BoxFace n m) : ℝ :=
  if f.2.2 then b f.1 f.2.1 else a f.1 f.2.1

def faceSet {n m : ℕ} (a b : Fin m → AngularSpace n) (f : BoxFace n m) :
    Set (AngularSpace n) :=
  f.2.1.insertNth (faceHeight a b f) ''
    Icc (a f.1 ∘ f.2.1.succAbove) (b f.1 ∘ f.2.1.succAbove)

def faceIntegral {n m : ℕ} (a b : Fin m → AngularSpace n)
    (F : AngularSpace n → Fin (n+1) → ℂ) (f : BoxFace n m) : ℂ :=
  ∫ x in Icc (a f.1 ∘ f.2.1.succAbove) (b f.1 ∘ f.2.1.succAbove),
    F (f.2.1.insertNth (faceHeight a b f) x) f.2.1

def signedFaceIntegral {n m : ℕ} (a b : Fin m → AngularSpace n)
    (F : AngularSpace n → Fin (n+1) → ℂ) (f : BoxFace n m) : ℂ :=
  if f.2.2 then faceIntegral a b F f else -faceIntegral a b F f

theorem sum_signedFaceIntegral {n m : ℕ} (a b : Fin m → AngularSpace n)
    (F : AngularSpace n → Fin (n+1) → ℂ) :
    (∑ f, signedFaceIntegral a b F f) = ∑ r, boundaryFlux (a r) (b r) F := by
  simp only [Fintype.sum_prod_type, signedFaceIntegral, Fintype.sum_bool,
    faceIntegral, faceHeight, Bool.false_eq_true, ↓reduceIte, boundaryFlux]
  simp only [sub_eq_add_neg]

/-- Geometric matching of a pair of faces. The last alternatives are the
two orientations of the exterior periodic identification. -/
structure FacesMatch {n m : ℕ} (lo hi : AngularSpace n)
    (a b : Fin m → AngularSpace n) (f g : BoxFace n m) : Prop where
  axis : f.2.1 = g.2.1
  lower : a f.1 ∘ f.2.1.succAbove = a g.1 ∘ g.2.1.succAbove
  upper : b f.1 ∘ f.2.1.succAbove = b g.1 ∘ g.2.1.succAbove
  opposite : f.2.2 = !g.2.2
  position : faceHeight a b f = faceHeight a b g ∨
    (faceHeight a b f = lo f.2.1 ∧ faceHeight a b g = hi g.2.1) ∨
    (faceHeight a b f = hi f.2.1 ∧ faceHeight a b g = lo g.2.1)

theorem FacesMatch.integral_eq {n m : ℕ} {lo hi : AngularSpace n}
    {a b : Fin m → AngularSpace n} {f g : BoxFace n m}
    (h : FacesMatch lo hi a b f g) (F : AngularSpace n → Fin (n+1) → ℂ)
    (hp : ∀ i x, F (i.insertNth (hi i) x) i = F (i.insertNth (lo i) x) i) :
    faceIntegral a b F f = faceIntegral a b F g := by
  unfold faceIntegral
  rw [h.lower, h.upper]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  rcases h.position with he | ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [he, h.axis]
  · rw [hl, hr, h.axis]
    exact (hp _ _).symm
  · rw [hl, hr, h.axis]
    exact hp _ _

theorem FacesMatch.signed_cancel {n m : ℕ} {lo hi : AngularSpace n}
    {a b : Fin m → AngularSpace n} {f g : BoxFace n m}
    (h : FacesMatch lo hi a b f g) (F : AngularSpace n → Fin (n+1) → ℂ)
    (hp : ∀ i x, F (i.insertNth (hi i) x) i = F (i.insertNth (lo i) x) i) :
    signedFaceIntegral a b F f = -signedFaceIntegral a b F g := by
  rw [signedFaceIntegral, signedFaceIntegral, h.integral_eq F hp, h.opposite]
  cases g.2.2 <;> simp

/-- A finite geometric cut. `mate` cancels all artificial and exterior faces;
the remaining faces are genuine boundary faces of the removed region. -/
structure PeriodicBoxCut (n : ℕ) (lo hi : AngularSpace n) where
  count : ℕ
  lower : Fin count → AngularSpace n
  upper : Fin count → AngularSpace n
  ordered : ∀ r, lower r ≤ upper r
  inside : ∀ r, Icc (lower r) (upper r) ⊆ Icc lo hi
  disjoint : Pairwise (fun r t => AEDisjoint volume
    (Icc (lower r) (upper r)) (Icc (lower t) (upper t)))
  puncture : BoxFace n count → Bool
  mate : Equiv.Perm (BoxFace n count)
  puncture_mate : ∀ f, puncture (mate f) = puncture f
  matched : ∀ f, puncture f = false → FacesMatch lo hi lower upper f (mate f)
  puncture_boundary : ∀ f, puncture f = true →
    faceSet lower upper f ⊆ frontier (Icc lo hi \ ⋃ r, Icc (lower r) (upper r))

def PeriodicBoxCut.domain {n : ℕ} {lo hi : AngularSpace n} (C : PeriodicBoxCut n lo hi) :
    Set (AngularSpace n) := ⋃ r, Icc (C.lower r) (C.upper r)

def PeriodicBoxCut.removed {n : ℕ} {lo hi : AngularSpace n} (C : PeriodicBoxCut n lo hi) :
    Set (AngularSpace n) := Icc lo hi \ C.domain

/-- Outward flux of the retained domain, hence inward toward the punctures. -/
def PeriodicBoxCut.punctureFlux {n : ℕ} {lo hi : AngularSpace n}
    (C : PeriodicBoxCut n lo hi) (F : AngularSpace n → Fin (n+1) → ℂ) : ℂ :=
  ∑ f, if C.puncture f then signedFaceIntegral C.lower C.upper F f else 0

theorem PeriodicBoxCut.boundary_eq_punctureFlux {n : ℕ} {lo hi : AngularSpace n}
    (C : PeriodicBoxCut n lo hi) (F : AngularSpace n → Fin (n+1) → ℂ)
    (hp : ∀ i x, F (i.insertNth (hi i) x) i = F (i.insertNth (lo i) x) i) :
    (∑ r, boundaryFlux (C.lower r) (C.upper r) F) = C.punctureFlux F := by
  classical
  let g := fun f => if C.puncture f then 0 else signedFaceIntegral C.lower C.upper F f
  have hg : ∀ f, g (C.mate f) = -g f := by
    intro f
    simp only [g, C.puncture_mate]
    cases hf : C.puncture f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      linear_combination (C.matched f hf).signed_cancel F hp
    · simp
  have hzero : (∑ f, g f) = 0 := by
    have he := Equiv.sum_comp C.mate g
    simp only [hg, Finset.sum_neg_distrib] at he
    linear_combination -(1 / 2 : ℂ) * he
  rw [← sum_signedFaceIntegral]
  calc
    _ = C.punctureFlux F + ∑ f, g f := by
      rw [PeriodicBoxCut.punctureFlux, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro f _
      cases hf : C.puncture f <;> simp [g, hf]
    _ = C.punctureFlux F := by rw [hzero, add_zero]

/-- A fixed angular cell with opposite faces identified, an open regular
locus, and increasing geometric excisions. The coverage field is a set
identity, not an integral convergence or differential identity. -/
structure PuncturedTorus (n : ℕ) where
  lower : AngularSpace n
  upper : AngularSpace n
  period : ∀ i, upper i = lower i + 2 * Real.pi
  regular : Set (AngularSpace n)
  regular_open : IsOpen regular
  regular_periodic : ∀ (z : Fin (n+1) → ℤ) x,
    x ∈ regular ↔ (fun i => x i + 2 * Real.pi * (z i : ℝ)) ∈ regular
  cut : ℕ → PeriodicBoxCut n lower upper
  monotone : Monotone (fun k => (cut k).domain)
  covers : (⋃ k, (cut k).domain) = Icc lower upper ∩ regular

def PuncturedTorus.domain {n : ℕ} (T : PuncturedTorus n) : Set (AngularSpace n) :=
  Icc T.lower T.upper ∩ T.regular

def PuncturedTorus.measure {n : ℕ} (T : PuncturedTorus n) : Measure (AngularSpace n) :=
  volume.restrict T.domain

theorem PuncturedTorus.domain_measurable {n : ℕ} (T : PuncturedTorus n) :
    MeasurableSet T.domain := measurableSet_Icc.inter T.regular_open.measurableSet

theorem PuncturedTorus.box_subset {n : ℕ} (T : PuncturedTorus n) (k : ℕ)
    (r : Fin (T.cut k).count) :
    Icc ((T.cut k).lower r) ((T.cut k).upper r) ⊆ T.domain := by
  intro x hx
  rw [PuncturedTorus.domain, ← T.covers]
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨r, hx⟩⟩

/-- The total oriented puncture-boundary flux at the kth excision. -/
def PuncturedTorus.punctureFlux {n : ℕ} (T : PuncturedTorus n)
    (F : AngularSpace n → Fin (n+1) → ℂ) (k : ℕ) : ℂ :=
  (T.cut k).punctureFlux F

/-- The source flux hypothesis: the actual surviving Stokes boundary sums
tend to zero along the geometric exhaustion. -/
def PuncturedTorus.VanishingFlux {n : ℕ} (T : PuncturedTorus n)
    (F : AngularSpace n → Fin (n+1) → ℂ) : Prop :=
  Tendsto (T.punctureFlux F) atTop (𝓝 0)

/-- Any fixed finite grouping of the surviving faces into punctures. Labels
on canceled faces have no effect. -/
def PuncturedTorus.componentFlux {n : ℕ} (T : PuncturedTorus n)
    {P : Type*} [DecidableEq P] (label : (k : ℕ) → BoxFace n (T.cut k).count → P)
    (F : AngularSpace n → Fin (n+1) → ℂ) (p : P) (k : ℕ) : ℂ :=
  ∑ f, if (T.cut k).puncture f then
    (if label k f = p then signedFaceIntegral (T.cut k).lower (T.cut k).upper F f else 0) else 0

theorem PuncturedTorus.sum_componentFlux {n : ℕ} (T : PuncturedTorus n)
    {P : Type*} [Fintype P] [DecidableEq P]
    (label : (k : ℕ) → BoxFace n (T.cut k).count → P)
    (F : AngularSpace n → Fin (n+1) → ℂ) (k : ℕ) :
    (∑ p, T.componentFlux label F p k) = T.punctureFlux F k := by
  unfold componentFlux punctureFlux PeriodicBoxCut.punctureFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  cases (T.cut k).puncture f <;> simp

theorem PuncturedTorus.vanishingFlux_of_components {n : ℕ} (T : PuncturedTorus n)
    {P : Type*} [Fintype P] [DecidableEq P]
    (label : (k : ℕ) → BoxFace n (T.cut k).count → P)
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (h : ∀ p, Tendsto (T.componentFlux label F p) atTop (𝓝 0)) : T.VanishingFlux F := by
  have hc := tendsto_finsetSum Finset.univ (fun p _ => h p)
  change Tendsto (fun k => T.punctureFlux F k) atTop (𝓝 0)
  simpa only [T.sum_componentFlux, Finset.sum_const_zero] using hc

theorem PuncturedTorus.integral_convergence {n : ℕ} (T : PuncturedTorus n)
    (f : AngularSpace n → ℂ) (hi : Integrable f T.measure) :
    Tendsto (fun k => ∑ r, ∫ x in Icc ((T.cut k).lower r) ((T.cut k).upper r), f x)
      atTop (𝓝 (∫ x, f x ∂T.measure)) := by
  have hc := rectangular_exhaustion_convergence f (fun k => (T.cut k).count)
    (fun k => (T.cut k).lower) (fun k => (T.cut k).upper)
    (fun k => (T.cut k).disjoint) T.monotone
  have he : (⋃ k, ⋃ r, Icc ((T.cut k).lower r) ((T.cut k).upper r)) = T.domain :=
    T.covers
  have hi' : IntegrableOn f T.domain := hi
  simpa only [he, PuncturedTorus.measure] using hc (by simpa only [he] using hi')

/-- The old analytic interface is constructed from geometry and regularity.
Neither integral convergence nor a derivative identity is assumed. -/
def PuncturedTorus.toFluxExhaustion {n : ℕ} (T : PuncturedTorus n)
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (hc : ∀ i, ContinuousOn (fun x => F x i) T.regular)
    (hd : ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => F y i) x)
    (hi : Integrable (divergence F) T.measure)
    (hp : ∀ i x, F (i.insertNth (T.upper i) x) i = F (i.insertNth (T.lower i) x) i)
    (hf : T.VanishingFlux F) : FluxExhaustion T.measure F where
  count := fun k => (T.cut k).count
  lower := fun k => (T.cut k).lower
  upper := fun k => (T.cut k).upper
  ordered := fun k => (T.cut k).ordered
  continuous := fun k r i => (hc i).mono (fun _ hx => (T.box_subset k r hx).2)
  differentiable := by
    intro k r x hx i
    apply hd x _ i
    apply (T.box_subset k r _).2
    exact ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩
  integrable := fun k r =>
    (show IntegrableOn (divergence F) T.domain volume from hi).mono_set (T.box_subset k r)
  convergence := T.integral_convergence _ hi
  flux_vanishes := by
    have he : (fun k => ∑ r, boundaryFlux ((T.cut k).lower r) ((T.cut k).upper r) F) =
        T.punctureFlux F := by
      funext k
      exact (T.cut k).boundary_eq_punctureFlux F hp
    rw [he]
    exact hf

theorem PuncturedTorus.integral_divergence_zero {n : ℕ} (T : PuncturedTorus n)
    (F : AngularSpace n → Fin (n+1) → ℂ)
    (hc : ∀ i, ContinuousOn (fun x => F x i) T.regular)
    (hd : ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => F y i) x)
    (hi : Integrable (divergence F) T.measure)
    (hp : ∀ i x, F (i.insertNth (T.upper i) x) i = F (i.insertNth (T.lower i) x) i)
    (hf : T.VanishingFlux F) : (∫ x, divergence F x ∂T.measure) = 0 :=
  (T.toFluxExhaustion F hc hd hi hp hf).integral_zero

end
end IsingBulk.Lie
