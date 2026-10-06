import IsingBulk.Algebra.SchurList
import IsingBulk.Algebra.SchurRational

/-! The exact Cayley substitution used in the manuscript's Schur proof. -/
namespace IsingBulk.Schur
noncomputable section

theorem pairProduct_map {F : Type*} [CommRing F] (K : F → F → F) (f : F → F) (xs : List F) :
    pairProduct K (xs.map f) = pairProduct (fun a b => K (f a) (f b)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairProduct, List.map_map, Function.comp_def, ih]

theorem pfaffian_map {F : Type*} [CommRing F] (K : F → F → F) (f : F → F)
    (n : ℕ) (xs : List F) :
    pfaffian K n (xs.map f) = pfaffian (fun a b => K (f a) (f b)) n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp [pfaffian, List.zipIdx_map, List.map_map, List.eraseIdx_map, Function.comp_def, ih]

theorem pairProduct_congr {F : Type*} [CommRing F] (A B : F → F → F) (xs : List F)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, A a b = B a b) : pairProduct A xs = pairProduct B xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [pairProduct, pairProduct, ih (fun b hb c hc => h b (by simp [hb]) c (by simp [hc]))]
    congr 1
    apply congrArg List.prod
    exact List.map_congr_left (fun b hb => h a (by simp) b (by simp [hb]))

theorem pfaffian_congr {F : Type*} [CommRing F] (A B : F → F → F) (n : ℕ) (xs : List F)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, A a b = B a b) : pfaffian A n xs = pfaffian B n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp only [pfaffian]
      congr 1
      apply List.map_congr_left
      rintro ⟨b,j⟩ hbj
      have hb : b ∈ xs := by
        rw [(List.mem_zipIdx' hbj).2]
        exact List.getElem_mem (List.mem_zipIdx' hbj).1
      dsimp only
      rw [h a (by simp) b (by simp [hb]), ih _ (fun c hc d hd =>
        h c (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hc))
          d (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hd)))]

def mobius {F : Type*} [Field F] (v : F) : F := (1+v)/(1-v)

theorem mobius_ne_zero {F : Type*} [Field F] {v : F} (h1 : v ≠ 1) (hm : v ≠ -1) :
    mobius v ≠ 0 := by
  apply div_ne_zero
  · intro h
    apply hm
    linear_combination h
  · exact sub_ne_zero.mpr h1.symm

theorem mobius_inj {F : Type*} [Field F] [CharZero F] {a b : F}
    (ha : a ≠ 1) (hb : b ≠ 1) (h : mobius a = mobius b) : a = b := by
  unfold mobius at h
  field_simp [sub_ne_zero.mpr ha.symm, sub_ne_zero.mpr hb.symm] at h
  linear_combination (1/2 : F) * h

theorem mobius_add {F : Type*} [Field F] {a b : F} (ha : a ≠ 1) (hb : b ≠ 1) :
    mobius a + mobius b = 2*(1-a*b)/((1-a)*(1-b)) := by
  unfold mobius
  field_simp [sub_ne_zero.mpr ha.symm, sub_ne_zero.mpr hb.symm]
  ring

theorem mobius_add_ne_zero {F : Type*} [Field F] [CharZero F] {a b : F}
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : 1-a*b ≠ 0) : mobius a + mobius b ≠ 0 := by
  rw [mobius_add ha hb]
  exact div_ne_zero (mul_ne_zero (by norm_num) hab)
    (mul_ne_zero (sub_ne_zero.mpr ha.symm) (sub_ne_zero.mpr hb.symm))

theorem mobius_kernel {F : Type*} [Field F] [CharZero F] {a b : F}
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : 1-a*b ≠ 0) :
    xKernel (mobius a) (mobius b) = (a-b)/(1-a*b) := by
  rw [xKernel, mobius_add ha hb]
  unfold mobius
  field_simp [sub_ne_zero.mpr ha.symm, sub_ne_zero.mpr hb.symm, hab]
  ring

theorem schur_fraction_of_nodup {F : Type*} [Field F] [CharZero F]
    (n : ℕ) (xs : List F) (hlen : xs.length = 2*n) (hn : xs.Nodup)
    (h1 : ∀ v ∈ xs, v ≠ 1) (hm : ∀ v ∈ xs, v ≠ -1)
    (hd : ∀ v ∈ xs, ∀ w ∈ xs, 1-v*w ≠ 0) :
    pfaffian (fun a b => (a-b)/(1-a*b)) n xs = pairProduct (fun a b => (a-b)/(1-a*b)) xs := by
  have hnodup : (xs.map mobius).Nodup := hn.map_on (fun a ha b hb he => mobius_inj (h1 a ha) (h1 b hb) he)
  have h := pfaffian_xKernel_of_nodup n (xs.map mobius) (by simpa using hlen) hnodup
    (by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      exact mobius_ne_zero (h1 v hv) (hm v hv))
    (by
      intro b hb c hc _
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      exact mobius_add_ne_zero (h1 v hv) (h1 w hw) (hd v hv w hw))
  rw [pfaffian_map, pairProduct_map] at h
  have he : ∀ a ∈ xs, ∀ b ∈ xs, xKernel (mobius a) (mobius b) = (a-b)/(1-a*b) :=
    fun a ha b hb => mobius_kernel (h1 a ha) (h1 b hb) (hd a ha b hb)
  rw [pfaffian_congr _ _ n xs he, pairProduct_congr _ _ xs he] at h
  exact h

theorem genericVariable_injective (n : ℕ) : Function.Injective (genericVariable n) := by
  intro i j h
  apply (MvPolynomial.X_injective (R := ℚ))
  exact IsFractionRing.injective (MvPolynomial (Fin (2*n)) ℚ) (RationalField n) h

theorem genericVariable_ne_one (n : ℕ) (i : Fin (2*n)) : genericVariable n i ≠ 1 := by
  have hp : (MvPolynomial.X i : MvPolynomial (Fin (2*n)) ℚ) ≠ 1 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) h
    norm_num at he
  have hh := (IsFractionRing.injective (MvPolynomial (Fin (2*n)) ℚ) (RationalField n)).ne hp
  simpa only [map_one, genericVariable] using hh

theorem genericVariable_ne_neg_one (n : ℕ) (i : Fin (2*n)) : genericVariable n i ≠ -1 := by
  have hp : (MvPolynomial.X i : MvPolynomial (Fin (2*n)) ℚ) ≠ -1 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) h
    norm_num at he
  have hh := (IsFractionRing.injective (MvPolynomial (Fin (2*n)) ℚ) (RationalField n)).ne hp
  simpa only [map_neg, map_one, genericVariable] using hh

/-- General even-N Schur identity as an equality of genuine rational functions. -/
theorem rationalIdentity (n : ℕ) : RationalIdentity n := by
  apply schur_fraction_of_nodup n (List.ofFn (genericVariable n)) (by simp)
    (List.nodup_ofFn.mpr (genericVariable_injective n))
  · intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact genericVariable_ne_one n i
  · intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact genericVariable_ne_neg_one n i
  · intro v hv w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact generic_denominator_ne_zero n i j

end
end IsingBulk.Schur
