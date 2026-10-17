import Bosonize.Core.A08OscillatorStates
namespace Bosonize.V1S1.Pairings
variable {α : Type*} [LinearOrder α]
def R (P : Finset (α×α)) (i j : α) : Prop := (i,j)∈P ∨ (j,i)∈P
def Good (V : Finset α) (P : Finset (α×α)) : Prop :=
  (∀ e∈P, e.1 < e.2) ∧
  ∀ i, (i∈V ↔ ∃j, R P i j) ∧ (∀ j k, R P i j → R P i k → j=k)
omit [LinearOrder α] in
lemma symm {P : Finset (α×α)} {i j : α} (h : R P i j) : R P j i := Or.symm h
lemma no_self {V : Finset α} {P : Finset (α×α)} (h : Good V P) (i : α) : ¬ R P i i := by
  intro hi
  have he : (i,i)∈P := hi.elim id id
  exact (lt_irrefl i) (h.1 _ he)
lemma erase_inc {V : Finset α} {P : Finset (α×α)} (h : Good V P)
    {x y : α} (hxy : (x,y)∈P) (i j : α) :
    R (P.erase (x,y)) i j ↔ R P i j ∧ i≠x ∧ i≠y ∧ j≠x ∧ j≠y := by
  have hlt : x<y := h.1 _ hxy
  have hR : R P x y := Or.inl hxy
  have hrev : (y,x) ∉ P := by
    intro he
    exact (not_lt_of_ge (le_of_lt hlt)) (h.1 _ he)
  have hu := fun a => (h.2 a).2
  constructor
  · intro hij
    have hijP : R P i j := by
      rcases hij with hij | hij
      · exact Or.inl (Finset.mem_of_mem_erase hij)
      · exact Or.inr (Finset.mem_of_mem_erase hij)
    have hx : i≠x := by
      intro he; subst i
      have hj := hu x j y hijP hR
      subst j
      simp [R, Finset.mem_erase, hrev, ne_of_gt hlt] at hij
    have hy : i≠y := by
      intro he; subst i
      have hj := hu y j x hijP (symm hR)
      subst j
      simp [R, Finset.mem_erase, hrev, ne_of_lt hlt] at hij
    have hjx : j≠x := by
      intro he; subst j
      exact hy (hu x i y (symm hijP) hR)
    have hjy : j≠y := by
      intro he; subst j
      exact hx (hu y i x (symm hijP) (symm hR))
    exact ⟨hijP,hx,hy,hjx,hjy⟩
  · rintro ⟨hij,hix,hiy,hjx,hjy⟩
    rcases hij with hij | hij
    · exact Or.inl (Finset.mem_erase.mpr ⟨by simp_all, hij⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨by simp_all, hij⟩)
lemma erase_good {V : Finset α} {P : Finset (α×α)} (h : Good V P)
    {x y : α} (hxy : (x,y)∈P) : Good ((V.erase x).erase y) (P.erase (x,y)) := by
  constructor
  · intro e he
    exact h.1 e (Finset.mem_of_mem_erase he)
  intro i
  have hR : R P x y := Or.inl hxy
  constructor
  · constructor
    · intro hi
      obtain ⟨hiy, hix, hiv⟩ : i≠y ∧ i≠x ∧ i∈V := by simpa using hi
      obtain ⟨j,hij⟩ := (h.2 i).1.mp hiv
      refine ⟨j,(erase_inc h hxy i j).mpr ⟨hij,hix,hiy,?_,?_⟩⟩
      · intro he; subst j
        exact hiy ((h.2 x).2 i y (symm hij) hR)
      · intro he; subst j
        exact hix ((h.2 y).2 i x (symm hij) (symm hR))
    · rintro ⟨j,hij⟩
      obtain ⟨hij,hix,hiy,_,_⟩ := (erase_inc h hxy i j).mp hij
      have hiv := (h.2 i).1.mpr ⟨j,hij⟩
      simp [hiv,hix,hiy]
  · intro j k hij hik
    exact (h.2 i).2 j k ((erase_inc h hxy i j).mp hij).1
      ((erase_inc h hxy i k).mp hik).1
lemma insert_R (P : Finset (α×α)) (x y i j : α) :
    R (insert (x,y) P) i j ↔ (i=x ∧ j=y) ∨ (i=y ∧ j=x) ∨ R P i j := by
  simp only [R, Finset.mem_insert, Prod.mk.injEq]
  tauto
lemma insert_good {V : Finset α} {P : Finset (α×α)} (h : Good V P)
    {x y : α} (hxy : x<y) (hx : x∉V) (hy : y∉V) :
    Good (insert x (insert y V)) (insert (x,y) P) := by
  have hne := ne_of_lt hxy
  constructor
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hxy
    · exact h.1 e he
  intro i
  have hxno (j : α) : ¬R P x j := by
    intro hh
    exact hx ((h.2 x).1.mpr ⟨j,hh⟩)
  have hyno (j : α) : ¬R P y j := by
    intro hh
    exact hy ((h.2 y).1.mpr ⟨j,hh⟩)
  by_cases hix : i=x
  · subst i
    simp only [Finset.mem_insert, true_or, true_iff, insert_R, true_and,
      hne, false_and, false_or, hxno, or_false]
    exact ⟨⟨y,rfl⟩, by intros; aesop⟩
  by_cases hiy : i=y
  · subst i
    simp only [Finset.mem_insert, true_or, or_true, true_iff, insert_R, true_and,
      Ne.symm hne, false_and, false_or, hyno, or_false]
    exact ⟨⟨x,rfl⟩, by intros; aesop⟩
  simp only [Finset.mem_insert, hix, hiy, false_or, insert_R, false_and]
  exact h.2 i
noncomputable def extendPair {S : Finset α} {x : α} (hx : x∉S)
    (hmin : ∀y∈S, x<y)
    (u : Σ y : {y // y∈S}, {P : Finset (α×α) // Good (S.erase y.val) P}) :
    {P : Finset (α×α) // Good (insert x S) P} := by
  classical
  refine ⟨insert (x,u.1.val) u.2.val, ?_⟩
  have h := insert_good u.2.property (hmin _ u.1.property)
    (show x∉S.erase u.1.val from fun hh => hx (Finset.mem_of_mem_erase hh))
    (Finset.notMem_erase _ _)
  simpa [Finset.insert_erase u.1.property] using h
lemma extendPair_bijective {S : Finset α} {x : α} (hx : x∉S)
    (hmin : ∀y∈S, x<y) : Function.Bijective (extendPair hx hmin) := by
  classical
  have absent (y : {y // y∈S}) (P : Finset (α×α)) (hP : Good (S.erase y.val) P) :
      (x,y.val)∉P := by
    intro hh
    exact hx (Finset.mem_of_mem_erase ((hP.2 x).1.mpr ⟨y.val, Or.inl hh⟩))
  constructor
  · intro u v huv
    have he := congrArg Subtype.val huv
    change insert (x,u.1.val) u.2.val = insert (x,v.1.val) v.2.val at he
    have hu := (extendPair hx hmin u).property
    have hR : R (extendPair hx hmin u).val x u.1.val := Or.inl (Finset.mem_insert_self _ _)
    have hR' : R (extendPair hx hmin u).val x v.1.val := by
      rw [huv]
      exact Or.inl (Finset.mem_insert_self _ _)
    have hy : u.1 = v.1 := Subtype.ext ((hu.2 x).2 _ _ hR hR')
    rcases u with ⟨y,P⟩
    rcases v with ⟨z,Q⟩
    dsimp at hy
    subst z
    have hpq : P = Q := Subtype.ext (by
      have hh := congrArg (fun W : Finset (α×α) => W.erase (x,y.val)) he
      simpa [Finset.erase_insert, absent y P.val P.property,
        absent y Q.val Q.property] using hh)
    subst Q
    rfl
  · intro P
    obtain ⟨y,hxy⟩ := (P.property.2 x).1.mp (Finset.mem_insert_self _ _)
    have hyV := (P.property.2 y).1.mpr ⟨x,symm hxy⟩
    have hne : y≠x := by
      intro he; subst y
      exact no_self P.property x hxy
    have hy : y∈S := (Finset.mem_insert.mp hyV).resolve_left hne
    have hedge : (x,y)∈P.val := by
      rcases hxy with hh | hh
      · exact hh
      · exact False.elim ((not_lt_of_ge (le_of_lt (hmin y hy))) (P.property.1 _ hh))
    have hrest := erase_good P.property hedge
    have hr : Good (S.erase y) (P.val.erase (x,y)) := by simpa [hx] using hrest
    refine ⟨⟨⟨y,hy⟩,⟨P.val.erase (x,y),hr⟩⟩, ?_⟩
    apply Subtype.ext
    exact Finset.insert_erase hedge
open scoped BigOperators
open Classical
noncomputable def sumOn [Fintype α] (C : α→α→ℂ) (V : Finset α) : ℂ := by
  classical
  exact ∑ P : {P : Finset (α×α) // Good V P}, ∏ e∈P.val, C e.1 e.2
lemma sumOn_first [Fintype α] (C : α→α→ℂ) (S : Finset α) (x : α)
    (hx : x∉S) (hmin : ∀y∈S,x<y) :
    sumOn C (insert x S) = ∑ y : {y // y∈S}, C x y.val * sumOn C (S.erase y.val) := by
  classical
  let E := Equiv.ofBijective (extendPair hx hmin) (extendPair_bijective hx hmin)
  have hweight (u : Σ y : {y // y∈S}, {P : Finset (α×α) // Good (S.erase y.val) P}) :
      (∏ e∈(E u).val, C e.1 e.2) = C x u.1.val * ∏ e∈u.2.val, C e.1 e.2 := by
    change (∏ e∈insert (x,u.1.val) u.2.val, C e.1 e.2) = _
    apply Finset.prod_insert
    intro hh
    exact hx (Finset.mem_of_mem_erase ((u.2.property.2 x).1.mpr ⟨u.1.val,Or.inl hh⟩))
  unfold sumOn
  rw [← E.sum_comp]
  simp_rw [hweight]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
lemma sumOn_as_sum [Fintype α] (C : α→α→ℂ) (V : Finset α) :
    sumOn C V = ∑ P : Finset (α×α), if Good V P then ∏e∈P, C e.1 e.2 else 0 := by
  classical
  unfold sumOn
  rw [← Finset.sum_subtype (Finset.univ.filter (Good V)) (by simp)
    (fun P : Finset (α×α) => ∏ e∈P, C e.1 e.2)]
  rw [Finset.sum_filter]
lemma sumOn_empty [Fintype α] (C : α→α→ℂ) : sumOn C ∅ = 1 := by
  classical
  have he (P : Finset (α×α)) : Good ∅ P ↔ P=∅ := by
    constructor
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hh := (h.2 e.1).1.mpr ⟨e.2,Or.inl he⟩
      simp at hh
    · rintro rfl
      simp [Good,R]
  rw [sumOn_as_sum]
  simp [he]
end Bosonize.V1S1.Pairings
