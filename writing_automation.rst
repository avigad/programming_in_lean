.. _Writing_Automation:

Writing Automation
==================

The goal of this chapter is to provide some examples that illustrate the
ways that metaprogramming in Lean can be used to implement automated
proof procedures.

A Tableau Prover for Classical Propositional Logic
--------------------------------------------------

In this section, we design a theorem prover that is complete for
classical propositional logic. The method is essentially that of
tableaux theorem proving, and, from a proof-theoretic standpoint, can be
used to demonstrate the completeness of cut-free sequent calculi.

The idea is simple. If ``a``, ``b``, ``c``, and ``d`` are formulas of
propositional logic, the sequent ``a, b, c ⊢ d`` represents the goal of
proving that ``d`` follows from ``a``, ``b`` and ``c``, and ``d``. The
fact that they are propositional formulas means that they are built up
from variables of type ``Prop`` and the constants ``true`` and ``false``
using the connectives ``∧ ∨ → ↔ ¬``. The proof procedure proceeds as
follows:

-  Negate the conclusion, so that the goal becomes ``a, b, c, ¬ d ⊢
    false``.

-  Put all formulas into *negation-normal form*. In other words,
   eliminate ``→`` and ``↔`` in terms of the other connectives, and
   using classical identities to push all equivalences inwards.

-  At that stage, all formulas are built up from *literals*
   (propositional variables and negated propositional variables) using
   only ``∧`` and ``∨``. Now repeatedly apply all of the following proof
   steps:

   -  Reduce a goal of the form ``Γ, a ∧ b ⊢ false`` to the goal
      ``Γ, a, b ⊢ false``, where ``Γ`` is any set of propositional
      formulas.

   -  Reduce a goal of the form ``Γ, a ∨ b ⊢ false`` to the pair of
      goals ``Γ, a ⊢ false`` and ``Γ, b ⊢ false``.

   -  Prove any goal of the form ``Γ, a, ¬ a ⊢ false`` in the usual way.

It is not hard to show that this is complete. Each step preserves
validity, in the sense that the original goal is provable if and only if
the new ones are. And, in each step, the number of connectives in the
goal decreases. If we ever face a goal in which the first two rules do
not apply, the goal must consist of literals. In that case, if the last
rule doesn't apply, then no propositional variable appears with its
negation, and it is easy to cook up a truth assignment that falsifies
the goal.

In fact, our procedure will work with arbitrary formulas at the leaves.
It simply applies reductions and rules as much as possible, so formulas
that begin with anything other than a propositional connective are
treated as black boxes, and act as propositional atoms.

First, let us open the namespaces we will use:

.. code-block:: lean

   open expr tactic classical

The next step is to gather all the facts we will need to put formulas in
negation-normal form.

.. code-block:: lean

   open expr tactic classical

   -- BEGIN
   section logical_equivalences
     local attribute [instance] prop_decidable
     variables {a b : Prop}

     theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
     iff.intro classical.by_contradiction not_not_intro

     theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
     iff.intro
       (λ h, if ha : a then or.inr (h ha) else or.inl ha)
       (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

     theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
     assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

     theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
     if ha : a then
       or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
     else
       or.inl ha

     theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
     iff.intro not_or_not_of_not_and not_and_of_not_or_not

     theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
     assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

     theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
     and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

     theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
     iff.intro not_and_not_of_not_or not_or_of_not_and_not
   end logical_equivalences
   -- END

We can now use Lean's built-in simplifier to do the normalization:

.. code-block:: lean

   open expr tactic classical

   section logical_equivalences
     local attribute [instance] prop_decidable
     variables {a b : Prop}

     theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
     iff.intro classical.by_contradiction not_not_intro.

     theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
     iff.intro
       (λ h, if ha : a then or.inr (h ha) else or.inl ha)
       (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

     theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
     assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

     theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
     if ha : a then
       or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
     else
       or.inl ha

     theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
     iff.intro not_or_not_of_not_and not_and_of_not_or_not

     theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
     assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

     theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
     and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

     theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
     iff.intro not_and_not_of_not_or not_or_of_not_and_not
   end logical_equivalences

   -- BEGIN
   meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
   do try (simp_at hyp lemmas)

   meta def normalize_hyps : tactic unit :=
   do hyps ← local_context,
      lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies, 
            ``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff, 
            ``not_true_iff, ``not_false_iff],
      monad.for' hyps (normalize_hyp lemmas)
   -- END

The tactic ``normalize_hyp`` just simplifies the given hypothesis with
the given list of lemmas. The ``try`` combinator ensures that the tactic
is deemed successful even if no simplifications are necessary. The
tactic ``normalize_hyps`` gathers the local context, turns the list of
names into a list of expressions by applying the ``mk_const`` tactic to
each one, and then calls ``normalize_hyp`` on each element of the
context with those lemmas. The ``for``' tactic, like the ``for`` tactic,
applies the second argument to each element of the first, but it returns
unit rather than accumulate the results in a list.

We can test the result:

.. code-block:: lean

   open expr tactic classical

   section logical_equivalences
     local attribute [instance] prop_decidable
     variables {a b : Prop}

     theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
     iff.intro classical.by_contradiction not_not_intro.

     theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
     iff.intro
       (λ h, if ha : a then or.inr (h ha) else or.inl ha)
       (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

     theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
     assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

     theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
     if ha : a then
       or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
     else
       or.inl ha

     theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
     iff.intro not_or_not_of_not_and not_and_of_not_or_not

     theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
     assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

     theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
     and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

     theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
     iff.intro not_and_not_of_not_or not_or_of_not_and_not
   end logical_equivalences

   meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
   do try (simp_at hyp lemmas)

   meta def normalize_hyps : tactic unit :=
   do hyps ← local_context,
      lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies, 
            ``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff, 
            ``not_true_iff, ``not_false_iff],
      monad.for' hyps (normalize_hyp lemmas)

   -- BEGIN
   example (p q r : Prop) (h₁ : ¬ (p ↔ (q ∧ ¬ r))) (h₂ : ¬ (p → (q → ¬ r))) : true :=
   by do normalize_hyps,
         trace_state,
         triv
   -- END

The result is as follows:

.. code-block:: text

   p q r : Prop,
   h₁ : p ∧ (r ∨ ¬q) ∨ q ∧ ¬p ∧ ¬r,
   h₂ : p ∧ q ∧ r
   ⊢ true

The next five tactics handle the task of splitting conjunctions.

.. code-block:: lean

   open tactic expr

   meta def add_fact (prf : expr) : tactic unit :=
   do nh ← get_unused_name `h none,
      p ← infer_type prf,
      assertv nh p prf,
      return ()

   meta def is_conj (e : expr) : tactic bool :=
   do t ← infer_type e,
      return (is_app_of t `and)

   meta def add_conjuncts : expr → tactic unit | e := 
   do e₁ ← mk_app `and.left [e],
      monad.cond (is_conj e₁) (add_conjuncts e₁) (add_fact e₁),
      e₂ ← mk_app `and.right [e],
      monad.cond (is_conj e₂) (add_conjuncts e₂) (add_fact e₂)

   meta def split_conjs_at (h : expr) : tactic unit :=
   do monad.cond (is_conj h) 
        (add_conjuncts h >> clear h)
        skip

   meta def split_conjs : tactic unit :=
   do l ← local_context,
      monad.for' l split_conjs_at

The tactic ``add_fact prf`` takes a proof of a proposition ``p``, and
adds ``p`` the the local context with a fresh name. Here,
:literal:`get_unused_name `h
none` generates a fresh name of the form ``h_n``, for a numeral ``n``.
The tactic ``is_conj`` infers the type of a given expression, and
determines whether or not it is a conjunction. The tactic
``add_conjuncts e`` assumes that the type of ``e`` is a conjunction and
adds proofs of the left and right conjuncts to the context, recursively
splitting them if they are conjuncts as well. The tactic
``split_conjs_at h`` tests whether or not the hypothesis ``h`` is a
conjunction, and, if so, adds all its conjuncts and then clears it from
the context. The last tactic, ``split_conjs``, applies this to every
element of the context.

We need two more small tactics before we can write our propositional
prover. The first reduces the task of proving a statement ``p`` from
some hypotheses to the task of proving falsity from those hypotheses and
the negation of ``p``.

.. code-block:: lean

   open tactic expr

   -- BEGIN
   meta def deny_conclusion : tactic unit :=
   do refine ```(classical.by_contradiction _),
      nh ← get_unused_name `h none,
      intro nh,
      return ()
   -- END

The refine tactic applies the expression in question to the goal, but
leaves any remaining metavariables for us to fill. The theorem
``classical.by_contradiction`` has type ``∀ {p : Prop},
(¬p → false) → p``, so applying this theorem proves the goal but leaves
us with the new goal of proving ``¬p → false`` from the same hypotheses,
at which point, we can use the introduction rule for implication. If we
omit the ``return ()``, we will get an error message, because
``deny_conclusion`` is supposed to have type ``tactic unit``, but the
``intro`` tactic returns an expression.

The next tactic finds a disjunction among the hypotheses, or returns the
``option.none`` if there aren't any.

.. code-block:: lean

   open tactic expr

   -- BEGIN
   meta def find_disj : tactic (option expr) :=
   do l ← local_context,
      (first $ l.map
        (λ h, do t ← infer_type h,
                 cond (is_app_of t `or) 
                   (return (option.some h)) failed)) <|>
      return none
   -- END

Our propositional prover can now be implemented as follows:

.. code-block:: lean

   open expr tactic classical

   section logical_equivalences
     local attribute [instance] prop_decidable
     variables {a b : Prop}

     theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
     iff.intro classical.by_contradiction not_not_intro.

     theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
     iff.intro
       (λ h, if ha : a then or.inr (h ha) else or.inl ha)
       (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

     theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
     assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

     theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
     if ha : a then
       or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
     else
       or.inl ha

     theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
     iff.intro not_or_not_of_not_and not_and_of_not_or_not

     theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
     assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

     theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
     and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

     theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
     iff.intro not_and_not_of_not_or not_or_of_not_and_not
   end logical_equivalences

   meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
   do try (simp_at hyp lemmas)

   meta def normalize_hyps : tactic unit :=
   do hyps ← local_context,
      lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies, 
            ``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff, 
            ``not_true_iff, ``not_false_iff],
      monad.for' hyps (normalize_hyp lemmas)

   meta def add_fact (prf : expr) : tactic unit :=
   do nh ← get_unused_name `h none,
      p ← infer_type prf,
      assertv nh p prf,
      return ()

   meta def is_conj (e : expr) : tactic bool :=
   do t ← infer_type e,
      return (is_app_of t `and)

   meta def add_conjuncts : expr → tactic unit | e := 
   do e₁ ← mk_app `and.left [e],
      monad.cond (is_conj e₁) (add_conjuncts e₁) (add_fact e₁),
      e₂ ← mk_app `and.right [e],
      monad.cond (is_conj e₂) (add_conjuncts e₂) (add_fact e₂)

   meta def split_conjs_at (h : expr) : tactic unit :=
   do monad.cond (is_conj h) 
        (add_conjuncts h >> clear h)
        skip

   meta def split_conjs : tactic unit :=
   do l ← local_context,
      monad.for' l split_conjs_at

   meta def deny_conclusion : tactic unit :=
   do refine ```(classical.by_contradiction _),
      nh ← get_unused_name `h none,
      intro nh,
      return ()

   meta def find_disj : tactic (option expr) :=
   do l ← local_context,
      (first $ l.map
        (λ h, do t ← infer_type h,
                 cond (is_app_of t `or)
                   (return (option.some h)) failed)) <|>
      return none

   -- BEGIN
   meta def prop_prover_aux : ℕ → tactic unit
   | 0            :=  fail "prop prover max depth reached"
   | (nat.succ n) :=
     do split_conjs,
        contradiction <|>
        do (option.some h) ← find_disj |
             fail "prop_prover failed: unprovable goal",
           cases h,
           prop_prover_aux n,
           prop_prover_aux n

   meta def prop_prover : tactic unit :=
   do deny_conclusion,
      normalize_hyps,
      prop_prover_aux 30
   -- END

The tactic ``prop_prover`` denies the conclusion, reduces the hypotheses
to negation-normal form, and calls ``prop_prover_aux`` with a maximum
splitting depth of 30. The tactic ``prop_prover_aux`` executes the
following simple loop. First, it splits any conjunctions in the
hypotheses. Then it tries applying the ``contradiction`` tactic, which
will find a pair of contradictory literals, ``p`` and ``¬ p``, if there
is one. If that does not succeed, it looks for a disjunction ``h`` among
the hypotheses. At this stage, if there aren't any disjunctions, we know
that the goal is not propositionally valid. On the other hand, if there
is a disjunction, ``prop_prover_aux`` calls the ``cases`` tactic to
split the disjunction, and then applies itself recursively to each of
the resulting subgoals, decreasing the splitting depth by one.

Notice the pattern matching in the ``do`` notation:

.. code-block:: text

   (option.some h) ← find_disj | 
             fail "prop_prover failed: unprovable goal"

This is shorthand for the use of the ``bind`` operation in the tactic
monad to extract the result of ``find_disj``, together with the use of a
``match`` statement to extract the result. The expression after the
vertical bar is the value returned for any other case in the pattern
match; in this case, it is the value returned if ``find_disj`` returns
``none``. This is a common idiom when writing tactics, and so the
compressed notation is handy.

All this is left for us to do is to try it out:

.. code-block:: lean

   open expr tactic classical

   section logical_equivalences
     local attribute [instance] prop_decidable
     variables {a b : Prop}

     theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
     iff.intro classical.by_contradiction not_not_intro.

     theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
     iff.intro
       (λ h, if ha : a then or.inr (h ha) else or.inl ha)
       (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

     theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
     assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

     theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
     if ha : a then
       or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
     else
       or.inl ha

     theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
     iff.intro not_or_not_of_not_and not_and_of_not_or_not

     theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
     assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

     theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
     and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

     theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
     iff.intro not_and_not_of_not_or not_or_of_not_and_not
   end logical_equivalences

   meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
   do try (simp_at hyp lemmas)

   meta def normalize_hyps : tactic unit :=
   do hyps ← local_context,
      lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies, 
            ``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff, 
            ``not_true_iff, ``not_false_iff],
      monad.for' hyps (normalize_hyp lemmas)

   meta def add_fact (prf : expr) : tactic unit :=
   do nh ← get_unused_name `h none,
      p ← infer_type prf,
      assertv nh p prf,
      return ()

   meta def is_conj (e : expr) : tactic bool :=
   do t ← infer_type e,
      return (is_app_of t `and)

   meta def add_conjuncts : expr → tactic unit | e := 
   do e₁ ← mk_app `and.left [e],
      monad.cond (is_conj e₁) (add_conjuncts e₁) (add_fact e₁),
      e₂ ← mk_app `and.right [e],
      monad.cond (is_conj e₂) (add_conjuncts e₂) (add_fact e₂)

   meta def split_conjs_at (h : expr) : tactic unit :=
   do monad.cond (is_conj h) 
        (add_conjuncts h >> clear h)
        skip

   meta def split_conjs : tactic unit :=
   do l ← local_context,
      monad.for' l split_conjs_at

   meta def deny_conclusion : tactic unit :=
   do refine ```(classical.by_contradiction _),
      nh ← get_unused_name `h none,
      intro nh,
      return ()

   meta def find_disj : tactic (option expr) :=
   do l ← local_context,
      (first $ l.map
        (λ h, do t ← infer_type h,
                 cond (is_app_of t `or)
                   (return (option.some h)) failed)) <|>
      return none

   meta def prop_prover_aux : ℕ → tactic unit
   | 0            :=  fail "prop prover max depth reached"
   | (nat.succ n) :=
     do split_conjs,
        contradiction <|>
        do (option.some h) ← find_disj |
             fail "prop_prover failed: unprovable goal",
           cases h,
           prop_prover_aux n,
           prop_prover_aux n

   meta def prop_prover : tactic unit :=
   do deny_conclusion,
      normalize_hyps,
      prop_prover_aux 30

   -- BEGIN
   section
     variables a b c d : Prop

     example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∨ c :=
     by prop_prover

     example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∧ ¬ c :=
     by prop_prover

     -- not valid
     -- example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∧ c :=
     -- by prop_prover

     example : ((a → b) → a) → a :=
     by prop_prover

     example : (a → b) ∧ (b → c) → a → c :=
     by prop_prover

     example (α : Type) (x y z w : α) :
       x = y ∧ (x = y → z = w) → z = w :=
     by prop_prover

     example : ¬ (a ↔ ¬ a) :=
     by prop_prover
   end
   -- END

