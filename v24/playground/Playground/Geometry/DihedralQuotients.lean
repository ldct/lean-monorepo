import Mathlib
import Mathlib.Tactic.GeneralizeProofs

set_option linter.style.longLine false

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

noncomputable section AristotleLemmas

/-
If a group G is generated by x and y with yxy^-1 = x^-1 and y^2 = 1, then every element in the closure is of the form x^n or yx^n.
-/
lemma mem_closure_of_generators_eq_zpow_or_mul_zpow {G : Type*} [Group G] (x y : G)
  (hconj : y * x * y⁻¹ = x⁻¹) (hy : y ^ 2 = 1)
  (g : G) (hg : g ∈ Subgroup.closure {x, y}) :
  ∃ n : ℤ, g = x ^ n ∨ g = y * x ^ n := by
    -- By definition of subgroup closure, $g$ can be written as a product of $x$ and $y$ and their inverses.
    have hg_prod : ∃ (l : List G), (∀ g ∈ l, g = x ∨ g = y ∨ g = x⁻¹ ∨ g = y⁻¹) ∧ g = List.prod l := by
      refine' Subgroup.closure_induction _ _ _ _ hg;
      · exact fun g hg => ⟨ [ g ], by aesop ⟩;
      · exact ⟨ [ ], by simp +decide ⟩;
      · rintro x y hx hy ⟨ l₁, hl₁, rfl ⟩ ⟨ l₂, hl₂, rfl ⟩ ; exact ⟨ l₁ ++ l₂, by aesop ⟩ ;
      · rintro g hg ⟨ l, hl, rfl ⟩;
        refine' ⟨ l.reverse.map fun g => g⁻¹, _, _ ⟩ <;> simp_all +decide [ List.prod_inv_reverse ];
        intro g hg; specialize hl g⁻¹; aesop;
    obtain ⟨l, hl⟩ := hg_prod;
    have h_prod_form : ∀ (l : List G), (∀ g ∈ l, g = x ∨ g = y ∨ g = x⁻¹ ∨ g = y⁻¹) → ∃ n : ℤ, List.prod l = x ^ n ∨ List.prod l = y * x ^ n := by
      intro l hl
      induction' l with g l ih;
      · exact ⟨ 0, by simp +decide ⟩;
      · rcases ih fun g hg => hl g ( List.mem_cons_of_mem _ hg ) with ⟨ n, hn | hn ⟩ <;> simp_all +decide [ pow_succ, mul_assoc ];
        · rcases hl.1 with ( rfl | rfl | rfl | rfl );
          · exact ⟨ n + 1, Or.inl ( by rw [ zpow_add, zpow_one ] ; group ) ⟩;
          · exact ⟨ n, Or.inr rfl ⟩;
          · exact ⟨ n - 1, Or.inl ( by group ) ⟩;
          · simp_all +decide [ mul_assoc, inv_eq_of_mul_eq_one_right hy ];
            exact ⟨ n, Or.inr rfl ⟩;
        · rcases hl.1 with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ ← mul_assoc ];
          · -- Using the relation $yxy^{-1} = x^{-1}$, we can rewrite $g * y$ as $y * g^{-1}$.
            have h_rewrite : g * y = y * g⁻¹ := by
              simp +decide [ ← hconj, mul_assoc ];
              simp +decide [ ← mul_assoc, hy ];
              rw [ inv_eq_of_mul_eq_one_right hy ];
            simp_all +decide [ mul_assoc, zpow_neg ];
            exact ⟨ n - 1, Or.inr ( by group ) ⟩;
          · exact ⟨ n, Or.inl rfl ⟩;
          · simp_all +decide [ mul_inv_eq_iff_eq_mul, ← hconj ];
            exact ⟨ n + 1, Or.inr ( by group ) ⟩;
          · exact ⟨ n, Or.inl rfl ⟩;
    aesop

/-
If G is generated by x and y with dihedral relations and y is not in the subgroup generated by x, then |G| = 2 * order(x).
-/
lemma card_eq_two_mul_orderOf_of_generators {G : Type*} [Group G] [Fintype G] (x y : G)
  (h_gen : ⊤ = Subgroup.closure {x, y})
  (hy : y ^ 2 = 1)
  (hconj : y * x * y⁻¹ = x⁻¹)
  (h_not_mem : y ∉ Subgroup.closure {x}) :
  Fintype.card G = 2 * orderOf x := by
    -- The elements of $G$ are of the form $x^k$ or $y x^k$ by `mem_closure_of_generators_eq_zpow_or_mul_zpow`.
    have h_elements : ∀ g : G, g ∈ Subgroup.closure {x, y} → ∃ n : ℤ, g = x ^ n ∨ g = y * x ^ n := by
      exact?;
    -- Since $y \notin H$, the cosets $H$ and $yH$ are disjoint.
    have h_disjoint : Disjoint (Set.image (fun n : ℤ => x ^ n) (Set.Ico 0 (orderOf x))) (Set.image (fun n : ℤ => y * x ^ n) (Set.Ico 0 (orderOf x))) := by
      rw [ Set.disjoint_left ];
      simp_all +decide [ Subgroup.mem_closure_singleton ];
      intro g n hn hn' hn'' m hm hm';
      contrapose! h_not_mem;
      refine' ⟨ n - m, _ ⟩;
      rw [ zpow_sub ] ; aesop;
    -- The union of $H$ and $yH$ is the entire group $G$.
    have h_union : Set.image (fun n : ℤ => x ^ n) (Set.Ico 0 (orderOf x)) ∪ Set.image (fun n : ℤ => y * x ^ n) (Set.Ico 0 (orderOf x)) = Set.univ := by
      ext g;
      simp +decide [ ← h_gen ] at h_elements ⊢;
      obtain ⟨ n, rfl | rfl ⟩ := h_elements g <;> [ left; right ] <;> use n % orderOf x <;> simp +decide [ zpow_mod_orderOf ];
      · exact ⟨ Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr ( ne_of_gt ( orderOf_pos x ) ) ), Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr ( orderOf_pos x ) ) ⟩;
      · exact ⟨ Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr ( ne_of_gt ( orderOf_pos x ) ) ), Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr ( orderOf_pos x ) ) ⟩;
    -- Since the images of $x^n$ and $yx^n$ are disjoint and their union is the entire group, the cardinality of the group is the sum of the cardinalities of these images.
    have h_card : Fintype.card G = Set.ncard (Set.image (fun n : ℤ => x ^ n) (Set.Ico 0 (orderOf x))) + Set.ncard (Set.image (fun n : ℤ => y * x ^ n) (Set.Ico 0 (orderOf x))) := by
      rw [ ← Set.ncard_union_eq h_disjoint, h_union, Set.ncard_univ ] ; simp +decide [ Set.ncard_univ ] ;
    rw [ h_card, Set.ncard_image_of_injOn, Set.ncard_image_of_injOn ];
    · simp +decide [ two_mul, Set.ncard_eq_toFinset_card' ];
    · intros a ha b hb hab;
      simp_all +decide [ zpow_eq_zpow_iff_modEq ];
      rw [ Int.ModEq ] at hab ; rw [ Int.emod_eq_of_lt, Int.emod_eq_of_lt ] at hab <;> linarith;
    · intros a ha b hb hab ; simp_all +decide [ zpow_eq_zpow_iff_modEq ];
      rw [ Int.ModEq ] at hab ; rw [ Int.emod_eq_of_lt, Int.emod_eq_of_lt ] at hab <;> linarith

/-
If yxy^-1 = x^-1, then yx^n = x^-n y for all integers n.
-/
lemma mul_zpow_eq_zpow_inv_mul_of_conjugation {G : Type*} [Group G] (x y : G)
  (hconj : y * x * y⁻¹ = x⁻¹) (n : ℤ) :
  y * x ^ n = x ^ (-n) * y := by
    have h_ind : ∀ n : ℕ, y * x ^ n * y⁻¹ = x⁻¹ ^ n := by
      intro n; induction n <;> simp_all +decide [ pow_succ, mul_assoc ] ;
      simp +decide only [← mul_assoc, ← ‹y * (x ^ _ * y⁻¹) = (x ^ _)⁻¹›, ← hconj];
      simp +decide [ mul_assoc ];
    rcases Int.eq_nat_or_neg n with ⟨ n, rfl | rfl ⟩ <;> simp_all +decide [ mul_inv_eq_iff_eq_mul ];
    have := h_ind n; simp_all +decide [ mul_assoc ] ;

/-
If x^m = 1 and m > 0, then x^((a+b).val) = x^a.val * x^b.val for a, b in ZMod m.
-/
lemma zpow_zmod_val_add {G : Type*} [Group G] (x : G) {m : ℕ} (hm : x ^ m = 1) (hm_pos : 0 < m) (a b : ZMod m) :
  x ^ (a + b).val = x ^ a.val * x ^ b.val := by
    -- Since $x^m = 1$, we have $x^{a.val + b.val} = x^{(a.val + b.val) \mod m}$.
    have h_exp : x ^ (a.val + b.val) = x ^ ((a.val + b.val) % m) := by
      rw [ ← Nat.mod_add_div ( a.val + b.val ) m, pow_add, pow_mul ] ; aesop;
    cases m <;> simp_all +decide [ ← pow_add ];
    simp_all +decide [ ZMod.val_add ]

/-
If x^m = 1 and m > 0, then x^((a-b).val) = x^a.val * (x^b.val)^-1 for a, b in ZMod m.
-/
lemma zpow_zmod_val_sub {G : Type*} [Group G] (x : G) {m : ℕ} (hm : x ^ m = 1) (hm_pos : 0 < m) (a b : ZMod m) :
  x ^ (a - b).val = x ^ a.val * (x ^ b.val)⁻¹ := by
    have zpow_zmod_val_add (a b : ZMod m) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
      exact?;
    have := zpow_zmod_val_add ( a - b ) b; aesop;

/-
Construct a homomorphism from DihedralGroup m to G.
-/
def dihedralHom {G : Type*} [Group G] [Finite G] (x y : G) (m : ℕ)
  (hm : orderOf x = m) (hy : y ^ 2 = 1) (hconj : y * x * y⁻¹ = x⁻¹) :
  DihedralGroup m →* G :=
  MonoidHom.mk' (fun g => match g with
    | DihedralGroup.r i => x ^ i.val
    | DihedralGroup.sr i => y * x ^ i.val)
    (by
    -- We need to show that the function is a homomorphism for all cases.
    intros a b
    cases' a with a ha
    cases' b with b hb;
    · convert zpow_zmod_val_add x _ _ _ _ using 1;
      · rw [ ← hm, pow_orderOf_eq_one ];
      · exact hm ▸ orderOf_pos x;
    · simp +decide [ pow_add, pow_one, mul_assoc, hy, hconj ];
      have h_comm : ∀ n : ℕ, y * x ^ n = x ^ (-n : ℤ) * y := by
        intro n
        induction' n with n ih;
        · simp +decide [ pow_zero ];
        · simp_all +decide [ zpow_add, zpow_neg, mul_assoc ];
          simp +decide [ ← mul_assoc, ← hconj, ← ih, pow_succ' ]
      have h_comm_z : ∀ n : ℤ, y * x ^ n = x ^ (-n : ℤ) * y := by
        exact?
      have h_comm_z_pow : y * x ^ (hb.val - a.val : ℤ) = x ^ (a.val - hb.val : ℤ) * y := by
        convert h_comm_z ( hb.val - a.val ) using 1 ; ring
      have h_comm_z_pow_eq : y * x ^ (hb - a).val = x ^ (a.val - hb.val : ℤ) * y := by
        have h_comm_z_pow_eq : (hb - a).val ≡ (hb.val - a.val : ℤ) [ZMOD m] := by
          cases m <;> simp +decide [ ← ZMod.intCast_eq_intCast_iff ];
          · exact absurd hm ( ne_of_gt ( orderOf_pos x ) );
          · erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
        rw [ ← h_comm_z_pow, ← zpow_natCast ];
        rw [ ← Int.emod_add_mul_ediv ( ( hb - a ).val : ℤ ) m, h_comm_z_pow_eq ] ; simp +decide [ zpow_add, zpow_mul, hm.symm ] ;
        rw [ ← Int.emod_add_mul_ediv ( ( hb.val : ℤ ) - a.val ) ( orderOf x ), zpow_add, zpow_mul ] ; simp +decide [ pow_orderOf_eq_one ]
      have h_comm_z_pow_eq' : x ^ (a.val - hb.val : ℤ) * y = x ^ a.val * (y * x ^ hb.val) := by
        simp +decide [ zpow_sub, mul_assoc, h_comm_z ];
        specialize h_comm hb.val; simp_all +decide [ mul_assoc, pow_succ ] ;
      grind +ring;
    · induction b with | r i => ?_ | sr i => ?_ <;> simp +decide [ *, mul_assoc ];
      · -- Since $x^m = 1$, we have $x^{(ha + i).val} = x^{ha.val + i.val}$.
        have h_exp : x ^ ((ha + i).val) = x ^ (ha.val + i.val) := by
          rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod.val_add ];
          · exact False.elim ( hm <| isOfFinOrder_iff_pow_eq_one.mpr ⟨ orderOf x, orderOf_pos x, pow_orderOf_eq_one x ⟩ );
          · rw [ ← Nat.mod_add_div ( ha.val + i.val ) ( m + 1 + 1 ), pow_add, pow_mul ] ; simp +decide [ hm.symm, pow_orderOf_eq_one ];
        rw [ h_exp, pow_add ];
      · have h_sub : x ^ (i - ha).val = x ^ i.val * (x ^ ha.val)⁻¹ := by
          convert zpow_zmod_val_sub x _ _ i ha;
          · rw [ ← hm, pow_orderOf_eq_one ];
          · exact hm ▸ orderOf_pos x;
        have h_conj : ∀ n : ℤ, y * x ^ n = x ^ (-n) * y := by
          exact?;
        have := h_conj ha.val; have := h_conj ( -i.val ) ; simp_all +decide [ ← mul_assoc ] ;
        simp_all +decide [ mul_assoc, sq ];
        group)

end AristotleLemmas

example (n : ℕ) (hn : 6 < n) (H : Subgroup (DihedralGroup n)) (hg : Subgroup.Normal H)
: IsDihedral (DihedralGroup n ⧸ H) ∨ IsCyclic (DihedralGroup n ⧸ H) := by
  have h_cases : ∀ {G : Type} [Group G] [Finite G], ∀ x y : G, orderOf x > 0 → y ^ 2 = 1 → y * x * y⁻¹ = x⁻¹ → (⊤ = Subgroup.closure { x, y }) → (y ∈ Subgroup.closure { x }) → IsCyclic G := by
    intros G _ _ x y hx hy hconj hgen hy_closure
    have h_cyclic : ∀ g : G, g ∈ Subgroup.closure { x, y } → g ∈ Subgroup.closure { x } := by
      simp_all +decide [ Subgroup.mem_closure ];
      exact fun g hg K hxK => hg K fun z hz => by aesop;
    exact ⟨ x, fun g => by have := h_cyclic g ( hgen ▸ Subgroup.mem_top g ) ; exact Subgroup.mem_closure_singleton.mp this ⟩;
  have h_cases : ∀ {G : Type} [Group G] [Finite G], ∀ x y : G, orderOf x > 0 → y ^ 2 = 1 → y * x * y⁻¹ = x⁻¹ → (⊤ = Subgroup.closure { x, y }) → (y ∉ Subgroup.closure { x }) → IsDihedral G := by
    intro G _ _ x y hx hy hconj hgen hy_not_mem
    use orderOf x
    generalize_proofs at *;
    have h_iso : Function.Bijective (dihedralHom x y (orderOf x) rfl hy hconj) := by
      have h_iso : Function.Surjective (dihedralHom x y (orderOf x) rfl hy hconj) := by
        intro g
        obtain ⟨n, hn⟩ : ∃ n : ℤ, g = x ^ n ∨ g = y * x ^ n := by
          have := mem_closure_of_generators_eq_zpow_or_mul_zpow x y hconj hy g ( hgen ▸ Subgroup.mem_top g ) ; tauto;
        rcases hn with ( rfl | rfl );
        · use DihedralGroup.r (n : ZMod (orderOf x));
          simp +decide [ dihedralHom ];
          rw [ ← zpow_mod_orderOf ];
          norm_num [ ZMod.val ];
          rcases k : orderOf x with ( _ | _ | k ) <;> simp_all +decide [ ZMod, Fin.ext_iff ];
          erw [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by linarith ) ) ];
        · use DihedralGroup.sr (n : ZMod (orderOf x));
          simp +decide [ dihedralHom ];
          rw [ ← zpow_mod_orderOf ];
          norm_num [ ZMod.val ];
          rcases k : orderOf x with ( _ | _ | k ) <;> simp_all +decide [ ZMod, Fin.ext_iff ];
          erw [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by linarith ) ) ];
      have h_card : Nat.card G = 2 * orderOf x := by
        convert card_eq_two_mul_orderOf_of_generators x y hgen hy hconj hy_not_mem using 1;
        convert Nat.card_eq_fintype_card;
        exact Fintype.ofFinite G;
      have h_card_eq : Nat.card (DihedralGroup (orderOf x)) = Nat.card G := by
        simp [h_card];
        cases orderOf x <;> simp_all +decide [ DihedralGroup.card ];
      have h_card_eq : Finite (DihedralGroup (orderOf x)) := by
        exact Nat.finite_of_card_ne_zero ( by rw [ h_card_eq, h_card ] ; positivity );
      have h_card_eq : Fintype (DihedralGroup (orderOf x)) := by
        exact Fintype.ofFinite _
      have h_card_eq : Fintype G := by
        exact Fintype.ofFinite G
      generalize_proofs at *;
      have := Fintype.bijective_iff_surjective_and_card ( dihedralHom x y ( orderOf x ) rfl hy hconj ) ; aesop;
    exact ⟨ { Equiv.ofBijective _ h_iso with map_mul' := fun a b => by simp +decide [ mul_assoc ] } ⟩;
  contrapose! h_cases;
  refine' ⟨ DihedralGroup n ⧸ H, inferInstance, _, _ ⟩;
  · cases n <;> [ tauto; exact? ];
  · -- Let $x$ be the image of $r$ and $y$ be the image of $s$ in the quotient group.
    obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : DihedralGroup n ⧸ H, orderOf x > 0 ∧ y ^ 2 = 1 ∧ y * x * y⁻¹ = x⁻¹ ∧ (⊤ = Subgroup.closure { x, y }) := by
      refine' ⟨ QuotientGroup.mk ( DihedralGroup.r 1 ), QuotientGroup.mk ( DihedralGroup.sr 0 ), _, _, _, _ ⟩ <;> norm_num [ orderOf_pos_iff ];
      · refine' isOfFinOrder_iff_pow_eq_one.mpr _;
        refine' ⟨ n, by linarith, _ ⟩;
        erw [ QuotientGroup.eq_one_iff ] ; aesop;
      · simp +decide [ sq ];
        erw [ QuotientGroup.eq_one_iff ] ; aesop;
      · erw [ QuotientGroup.eq ] ; aesop;
      · refine' eq_comm.mp ( Subgroup.closure_eq_of_le _ _ _ );
        · exact Set.subset_univ _;
        · intro x hx;
          obtain ⟨ x, rfl ⟩ := QuotientGroup.mk_surjective x;
          induction x using DihedralGroup.rec <;> simp_all +decide [ Subgroup.mem_closure ];
          · intro K hK;
            rename_i a ha;
            convert K.pow_mem ( hK ( Set.mem_insert _ _ ) ) a.val using 1;
            rcases n with ( _ | _ | n ) <;> norm_cast;
            erw [ QuotientGroup.eq ];
            simp +decide [ ← pow_mul, ← pow_add ];
          · intro K hK; simp_all +decide [ Set.insert_subset_iff ] ;
            rename_i a ha;
            convert K.mul_mem hK.2 ( K.pow_mem hK.1 a.val ) using 1;
            erw [ QuotientGroup.eq ];
            cases n <;> aesop;
    refine' ⟨ x, y, hx, hy, hxy.1, hxy.2, _, _ ⟩;
    · intro hy_mem;
      refine' h_cases.2 _;
      have h_cyclic : Subgroup.closure { x } = ⊤ := by
        simp_all +decide [ Subgroup.closure ];
        congr with K ; simp +decide [ Set.insert_subset_iff, hy_mem ];
        exact hy_mem K;
      use x;
      intro g;
      have := Subgroup.mem_closure_singleton.mp ( h_cyclic.symm ▸ Subgroup.mem_top g ) ; tauto;
    · exact h_cases.1
