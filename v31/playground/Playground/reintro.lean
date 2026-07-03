-- from https://github.com/emilyriehl/ReintroductionToProofs
-- this file explicitly does not depend on Mathlib, batteries, etc

set_option linter.unusedVariables false

-- TypeWorld/L01_Elements
example {A : Type} (a : A) : A := by
  -- Hint (hidden := true) "Type `assumption` to tell Lean to use the assumed element of `A` to define an element of `A`."
  assumption

-- TypeWorld/L02_Proofs
example {P : Prop} (p : P) : P := by
  -- Hint (hidden := true) "Type `assumption` to tell Lean to use the assumption that `P` is true to conclude that `P` is true."
  assumption

-- TypeWorld/L03_ExactElements
/-- Under the hypothesis that we have types `A` and `B` and elements `x : A` and `y z : B`, we may define an element of type `B`. -/
example {A B : Type} (x : A) (y z : B) : B := by
  exact z
  -- "After solving this level, use the `Retry` button to solve it again. What happens if you try `exact x`?"

-- TypeWorld/L04_UnitType
example : Unit := by
  exact ⟨⟩

-- TypeWorld/L05_TypeOfPropositions
/-- The type of propositions `Prop` contains propositions like `True`. -/
example (P Q : Prop) (p : P) : Prop := by
  exact Q

-- TypeWorld/L06_TypeOfTypes
example : Type := by
  -- Hint (hidden := true) "In the previous level, we introduced the type `Unit`. This is an element of the type `Type`, so you can solve this level by typing `exact Unit`."
  exact Unit

-- TypeWorld/L07_BossLevel
/-- Define an element of `Type` in a nontrivial context. -/
example (P Q R : Prop) (q : Q) (r : R) : Type := by
  exact Prop

-- FunctionWorld/L01_IdentityFunction
example {A : Type} : A → A := by
  -- Hint (hidden := true) "To define a function, in this case an element of type `{A} → {A}`, one must define a rule to convert an arbitrary element `x : {A}` to some element of type `{A}`. Start by typing `intro x` to add an arbitrary element of type `{A}` to the context."
  intro x
  -- Hint (hidden := true) "Now the goal is an element of type `{A}`, which should be thought of as result of applying the function to the element `{x} : {A}`. In the case of the identity function, we want to return `{x} : {A}` again which is done by typing `exact {x}`."
  exact x

-- FunctionWorld/L02_UsingFunctions
/-- Apply a function to an argument. -/
example {A B : Type} (a : A) (f : A → B) : B := by
  exact f a

-- FunctionWorld/L03_UsingFunctionsBackwards
/-- Using `apply` to work backwards from the goal. -/
example {A B : Type} (a : A) (f : A → B) : B := by
  apply f
  exact a

-- FunctionWorld/L04_ComposingFunctions
/-- Composing two functions. -/
example {A B C : Type} (g : B → C) (f : A → B) : A → C := by
  intro x
  exact g (f x)

-- FunctionWorld/L05_ConstantFunctions
/-- The constant function. -/
example {A B : Type} (a : A) : B → A := by
  exact fun _ ↦ a

-- FunctionWorld/L06_MultivariableFunctions
/-- Multivariable functions. -/
example {A B C : Type} (a : A) (f : A → B → C) : B → C := by
  intro b
  apply f
  · exact a
  · exact b

-- FunctionWorld/L07_SwappingInputs
/-- Swapping the inputs of a binary function. -/
example {A B C : Type} : (A → B → C) → (B → A → C) := by
  intro f
  intro b
  intro a
  exact f a b

-- FunctionWorld/L08_CompositionRevisited
/-- Composition as a multivariable function between function types. -/
example {A B C : Type} : (B → C) → (A → B) → (A → C) := by
  intro g f a
  exact g (f a)

-- FunctionWorld/L09_Evaluation
/-- Evaluation. -/
example {A B : Type} : A → (A → B) → B := by
  intro a
  intro f
  exact f a

-- FunctionWorld/L10_BossLevel
/-- A higher-order continuation-style construction. -/
example {F V : Type} : ((((V → F) → F) → F) → F) → ((V → F) → F) := by
  intro μ
  intro φ
  apply μ
  intro α
  apply α
  exact φ

-- ImplicationWorld/L01_ByAssumption
/-- If `P` is true, then `P` is true. -/
example {P : Prop} (p : P) : P := by
  exact p

-- ImplicationWorld/L02_ModusPonens
/-- Modus ponens: from `P` and `P → Q`, deduce `Q`. -/
example {P Q : Prop} (p : P) (h : P → Q) : Q := by
  apply h
  exact p

-- ImplicationWorld/L03_ApplyingImplication
/-- Modus ponens again, this time by direct application. -/
example {P Q : Prop} (p : P) (h : P → Q) : Q := by
  exact h p

-- ImplicationWorld/L04_ComposingImplication
/-- Composing implications: from `P`, `P → Q`, and `Q → R`, deduce `R`. -/
example {P Q R : Prop} (p : P) (h1 : P → Q) (h2 : Q → R) : R := by
  apply h2
  apply h1
  exact p

-- ImplicationWorld/L05_ProvingImplication
/-- For any proposition `P`, `P → P`. -/
example {P : Prop} : P → P := by
  intro p
  exact p

-- ImplicationWorld/L06_ProvingImpliedAssumption
/-- If `P` is true, then `Q → P` for any `Q`. -/
example {P Q : Prop} (p : P) : Q → P := by
  intro _
  exact p

-- ImplicationWorld/L07_ProvingAssumedImplication
/-- `P → Q` implies `P → Q`. -/
example {P Q : Prop} (h : P → Q) : P → Q := by
  exact h

-- ImplicationWorld/L08_Transitivity
/-- Transitivity of implication. -/
example {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by
  intro h1 h2 p
  apply h2
  apply h1
  exact p

-- ImplicationWorld/L09_ModusPonensAgain
/-- Modus ponens packaged as a propositional formula. -/
example {P Q : Prop} : P → (P → Q) → Q := by
  intro p h
  apply h
  exact p

-- ImplicationWorld/L10_BossLevel
/-- A long chain of implications. -/
example {P Q R S T U V W X Y Z : Prop} :
    (S → X) → (T → W) → (R → Y) → (W → Q) → (U → S) → (Y → T) →
    (X → V) → (Q → U) → (V → Z) → (P → R) → P → Z := by
  intro sx tw ry wq us yt xv qu vz pr p
  apply vz
  apply xv
  apply sx
  apply us
  apply qu
  apply wq
  apply tw
  apply yt
  apply ry
  apply pr
  exact p

-- ProductWorld/L01_Pairing
/-- Pairing elements to form a product. -/
example {A B : Type} (a : A) (b : B) : A × B := by
  exact ⟨a, b⟩

-- ProductWorld/L02_FirstProjection
/-- First projection. -/
example {A B : Type} : A × B → A := by
  intro p
  exact p.1

-- ProductWorld/L03_SecondProjection
/-- Second projection. -/
example {A B : Type} : A × B → B := by
  intro p
  exact p.2

-- ProductWorld/L04_Symmetry
/-- Symmetry of product types. -/
example {A B : Type} : A × B → B × A := by
  intro p
  exact ⟨p.2, p.1⟩

-- ProductWorld/L05_Associativity
/-- Associativity of product types. -/
example {A B C : Type} :
    ((A × B) × C → A × (B × C)) × (A × (B × C) → (A × B) × C) := by
  refine ⟨?_, ?_⟩
  · intro p
    exact ⟨p.1.1, p.1.2, p.2⟩
  · intro p
    exact ⟨⟨p.1, p.2.1⟩, p.2.2⟩

-- ProductWorld/L06_Currying
/-- Currying a function out of a product. -/
example {A B C : Type} : (A × B → C) → (A → B → C) := by
  intro f a b
  exact f ⟨a, b⟩

-- ProductWorld/L07_Uncurrying
/-- Uncurrying a binary function. -/
example {A B C : Type} : (A → B → C) → (A × B → C) := by
  intro f p
  exact f p.1 p.2

-- ProductWorld/L08_ComponentFunctions
/-- A function into a product splits into component functions. -/
example {X A B : Type} : (X → A × B) → (X → A) × (X → B) := by
  intro f
  refine ⟨?_, ?_⟩
  · intro x; exact (f x).1
  · intro x; exact (f x).2

-- ProductWorld/L09_UniversalProperty
/-- Combining two functions into one into a product. -/
example {X A B : Type} : (X → A) × (X → B) → (X → A × B) := by
  intro f x
  exact ⟨f.1 x, f.2 x⟩

-- ProductWorld/L10_BossLevel
/-- A wiring puzzle through several product types. -/
example {A B C D E M N X Y Z : Type} :
    (B × D → M) → (E → Y × N) → (A → M → X) → (C → N → Z) →
    (A × B × C × D × E → X × Y × Z) := by
  intro f g h k p
  exact ⟨h p.1 (f ⟨p.2.1, p.2.2.2.1⟩),
         (g p.2.2.2.2).1,
         k p.2.2.1 (g p.2.2.2.2).2⟩

-- ConjunctionWorld/L01_IntroducingAnd
/-- Introducing `∧`. -/
example {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  exact ⟨p, q⟩

-- ConjunctionWorld/L02_UsingAnd
/-- Reusing a conjunction. -/
example {P Q : Prop} (h : P ∧ Q) : P ∧ Q := by
  exact ⟨h.1, h.2⟩

-- ConjunctionWorld/L03_Symmetry
/-- Symmetry of `∧`. -/
example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.2, h.1⟩

-- ConjunctionWorld/L04_LogicalEquivalence
/-- `P ∧ Q ↔ Q ∧ P`. -/
example {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro k; exact ⟨k.2, k.1⟩

-- ConjunctionWorld/L05_Associativity
/-- Associativity of `∧`. -/
example {P Q R : Prop} : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro k
    exact ⟨⟨k.1, k.2.1⟩, k.2.2⟩

-- ConjunctionWorld/L06_CompoundImplication
/-- Currying for `∧`. -/
example {P Q R : Prop} (h : P ∧ Q → R) : P → Q → R := by
  intro p q
  apply h
  exact ⟨p, q⟩

-- ConjunctionWorld/L07_MoreCompoundImplication
/-- Uncurrying for `∧`. -/
example {P Q R : Prop} (h : P → Q → R) : P ∧ Q → R := by
  intro pq
  apply h
  · exact pq.1
  · exact pq.2

-- ConjunctionWorld/L08_CurryingImplication
/-- Currying as a logical equivalence. -/
example {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h p q; exact h ⟨p, q⟩
  · intro h pq; exact h pq.1 pq.2

-- ConjunctionWorld/L09_UniversalProperty
/-- Universal property of `∧` in the codomain. -/
example {P Q R : Prop} : (P → Q) ∧ (P → R) ↔ P → Q ∧ R := by
  constructor
  · intro gh p
    exact ⟨gh.1 p, gh.2 p⟩
  · intro h
    exact ⟨fun p ↦ (h p).1, fun p ↦ (h p).2⟩

-- ConjunctionWorld/L10_BossLevel
/-- A wiring puzzle through several conjunctions. -/
example {P Q R S T U V W X Y Z : Prop} :
    P → (R → S ∧ T) → (U → P → R) → ((U → Y) → Z) →
    (W ∧ T ∧ V → X ∧ Y) → (S → V ∧ W) → Z := by
  intro p h k l g f
  apply l
  intro u
  have hst := h (k u p)
  have fvw := f hst.1
  exact (g ⟨fvw.2, hst.2, fvw.1⟩).2

-- CoproductWorld/L01_LeftInclusion
/-- Left inclusion into a coproduct. -/
example {A B : Type} (a : A) : A ⊕ B := by
  left
  exact a

-- CoproductWorld/L02_RightInclusion
/-- Right inclusion into a coproduct. -/
example {A B : Type} (b : B) : A ⊕ B := by
  apply Sum.inr
  exact b

-- CoproductWorld/L03_ComponentFunctions
/-- A function out of a coproduct splits into component functions. -/
example {A B C : Type} : (A ⊕ B → C) → (A → C) × (B → C) := by
  intro f
  exact ⟨fun a ↦ f (Sum.inl a), fun b ↦ f (Sum.inr b)⟩

-- CoproductWorld/L04_UniversalProperty
/-- Two functions assemble into a single function out of a coproduct. -/
example {A B C : Type} (g : A → C) (h : B → C) : A ⊕ B → C := by
  intro x
  cases x with
  | inl a => exact g a
  | inr b => exact h b

-- CoproductWorld/L05_Symmetry
/-- Symmetry of coproduct types. -/
example {A B : Type} : A ⊕ B → B ⊕ A := by
  intro x
  cases x with
  | inl a => exact Sum.inr a
  | inr b => exact Sum.inl b

-- CoproductWorld/L06_Associativity
/-- Associativity of coproduct types. -/
example {A B C : Type} :
    ((A ⊕ B) ⊕ C → A ⊕ (B ⊕ C)) × (A ⊕ (B ⊕ C) → (A ⊕ B) ⊕ C) := by
  refine ⟨?_, ?_⟩
  · intro p
    cases p with
    | inl ab =>
      cases ab with
      | inl a => exact Sum.inl a
      | inr b => exact Sum.inr (Sum.inl b)
    | inr c => exact Sum.inr (Sum.inr c)
  · intro p
    cases p with
    | inl a => exact Sum.inl (Sum.inl a)
    | inr bc =>
      cases bc with
      | inl b => exact Sum.inl (Sum.inr b)
      | inr c => exact Sum.inr c

-- CoproductWorld/L07_Distributivity
/-- Product distributes over coproduct. -/
example {A B C : Type} :
    (A × (B ⊕ C) → (A × B) ⊕ (A × C)) × ((A × B) ⊕ (A × C) → A × (B ⊕ C)) := by
  refine ⟨?_, ?_⟩
  · intro p
    cases p.2 with
    | inl b => exact Sum.inl ⟨p.1, b⟩
    | inr c => exact Sum.inr ⟨p.1, c⟩
  · intro p
    cases p with
    | inl q => exact ⟨q.1, Sum.inl q.2⟩
    | inr r => exact ⟨r.1, Sum.inr r.2⟩

-- CoproductWorld/L08_BossLevel
/-- Functions out of a coproduct into a product decompose into four components. -/
example {A B C D : Type} :
    ((A ⊕ B → C × D) → (A → C) × (B → C) × (A → D) × (B → D)) ×
      ((A → C) × (B → C) × (A → D) × (B → D) → (A ⊕ B → C × D)) := by
  refine ⟨?_, ?_⟩
  · intro f
    exact ⟨fun a ↦ (f (Sum.inl a)).1,
           fun b ↦ (f (Sum.inr b)).1,
           fun a ↦ (f (Sum.inl a)).2,
           fun b ↦ (f (Sum.inr b)).2⟩
  · intro p x
    cases x with
    | inl a => exact ⟨p.1 a, p.2.2.1 a⟩
    | inr b => exact ⟨p.2.1 b, p.2.2.2 b⟩

-- DisjunctionWorld/L01_IntroducingOr
/-- Introducing `∨`. -/
example {P Q : Prop} (p : P) (q : Q) : P ∨ Q := by
  left
  exact p

-- DisjunctionWorld/L02_AndImpliesOr
/-- `P ∧ Q` implies `P ∨ Q`. -/
example {P Q : Prop} : P ∧ Q → P ∨ Q := by
  intro h
  exact Or.inl h.1

-- DisjunctionWorld/L03_UsingOr
/-- Case-splitting on a disjunction. -/
example {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl p => exact Or.inr p
  | inr q => exact Or.inl q

-- DisjunctionWorld/L04_Symmetry
/-- Symmetry of `∨`. -/
example {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl p => exact Or.inr p
    | inr q => exact Or.inl q
  · intro h
    cases h with
    | inl q => exact Or.inr q
    | inr p => exact Or.inl p

-- DisjunctionWorld/L05_UniversalProperty
/-- Universal property of `∨` in the domain. -/
example {P Q R : Prop} : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by
  constructor
  · intro h
    exact ⟨fun p ↦ h (Or.inl p), fun q ↦ h (Or.inr q)⟩
  · intro h k
    cases k with
    | inl p => exact h.1 p
    | inr q => exact h.2 q

-- DisjunctionWorld/L06_Associativity
/-- Associativity of `∨`. -/
example {P Q R : Prop} : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro hpqr
    cases hpqr with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro hpqr
    cases hpqr with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- DisjunctionWorld/L07_Distributivity
/-- Conjunction distributes over disjunction. -/
example {P Q R : Prop} : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    cases h.2 with
    | inl q => exact Or.inl ⟨h.1, q⟩
    | inr r => exact Or.inr ⟨h.1, r⟩
  · intro h
    cases h with
    | inl pq => exact ⟨pq.1, Or.inl pq.2⟩
    | inr pr => exact ⟨pr.1, Or.inr pr.2⟩

-- DisjunctionWorld/L08_MoreDistributivity
/-- `(P ∨ Q) ∧ (R ∨ S) ↔ (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)`. -/
example {P Q R S : Prop} :
    (P ∨ Q) ∧ (R ∨ S) ↔ (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  constructor
  · intro h
    cases h.1 with
    | inl p =>
      cases h.2 with
      | inl r => exact Or.inl ⟨p, r⟩
      | inr s => exact Or.inr (Or.inl ⟨p, s⟩)
    | inr q =>
      cases h.2 with
      | inl r => exact Or.inr (Or.inr (Or.inl ⟨q, r⟩))
      | inr s => exact Or.inr (Or.inr (Or.inr ⟨q, s⟩))
  · intro h
    cases h with
    | inl pr => exact ⟨Or.inl pr.1, Or.inl pr.2⟩
    | inr h =>
      cases h with
      | inl ps => exact ⟨Or.inl ps.1, Or.inr ps.2⟩
      | inr h =>
        cases h with
        | inl qr => exact ⟨Or.inr qr.1, Or.inl qr.2⟩
        | inr qs => exact ⟨Or.inr qs.1, Or.inr qs.2⟩

-- DisjunctionWorld/L09_BossLevel
/-- A wiring puzzle combining conjunction and disjunction. -/
example {P Q R S T U V W X Y Z : Prop} :
    (T ∨ U → V ∧ Y) → (Q → P → T) → (Y → Q → W) →
    ((V ∧ W) ∨ (X ∧ Y) → Z) → (R → S → U) ∧ (V → R → X) →
    P ∧ (Q ∨ R) ∧ S → Z := by
  intro f g h j k pqrs
  apply j
  cases pqrs.2.1 with
  | inl q =>
    apply Or.inl
    have t := g q pqrs.1
    have vy := f (Or.inl t)
    have w := h vy.2 q
    exact ⟨vy.1, w⟩
  | inr r =>
    apply Or.inr
    have u := k.1 r pqrs.2.2
    have vy := f (Or.inr u)
    have x := k.2 vy.1 r
    exact ⟨x, vy.2⟩
