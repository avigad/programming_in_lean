.. _Writing_Tactics:

Writing Tactics
===============

A First Look at the Tactic Monad
--------------------------------

The canonical way to invoke a tactic in Lean is to use the ``by``
keyword within a Lean expression. Suppose we write the following:

.. code-block:: text

   open tactic

   variables a b : Prop

   example : a → b → a ∧ b :=
   by _

Lean expects something of type ``tactic unit`` to fill the underscore,
where ``tactic`` refers to the tactic monad. When the elaborator
processes this definition, it elaborates everything outside the ``by``
invocation first (in this case, just the statement of the theorem), and
then calls on the Lean virtual machine to execute the tactic. When doing
so, the virtual machine interprets any axiomatically declared
``meta constant`` as references to internal Lean functions that
implement the functionality of the tactic monad.

The tactic monad can be thought of as a combination of a state monad
(where the internal "state" as accessed and acted on by the
``meta constant`` primitives) and the option monad. Because it is a
monad, we have the usual ``do`` notation. So, if ``r``, ``s``, and ``t``
are tactics, you should think of

.. code-block:: text

   do a ← r, 
      b ← s,
      t

as meaning "apply tactic ``r`` to the state, and store the return result
in ``a``; apply tactic ``s`` to the state, and store the return result
in ``b``; then, finally, apply tactic ``t`` to the state." Moreover, any
tactic can *fail*, which is analogous to a return value of ``none`` in
the option monad. In the example above, if any of ``r``, ``s``, or ``t``
fail, then the compound expression has failed.

There is an additional, really interesting feature of the tactic monad:
it is an *alternative* monad, in the sense described at the end of the
last chapter. This is used to implement backtracking. If ``s`` and ``t``
are monads, the expression ``s <|> t`` can be understood as follows: "do
``s``, and if that succeeds, return the corresponding return value;
otherwise, undo any changes to the state that ``s`` may have produced,
and do ``t`` instead." This allows us to try ``s`` and, if it fails, go
on to try ``t`` as though the first attempt never happened.

When the tactic expression after a ``by`` is invoked, the tactic wakes
up and says "Whoa! I'm in a monad!" This is just a colorful way of
saying that the virtual machine expects a function that acts on the
tactic state in a certain way, and interprets primitive operations on
the tactic state in terms of functions that are implemented internal to
Lean. At any rate, when it wakes up, it can start to look around and
assess its current state. The goal of this section is to give you a
first look at of some of the things it can do there. Don't worry if some
of the expressions seem mysterious; they will be explained in the
sections that follow.

One thing the tactic can do is print a message to the outside world:

.. code-block:: text

   example : a → b → a ∧ b :=
   by do trace "Hi, Mom!"

When the file is executed, Lean issues an error message to the effect
that the tactic has failed to fill the relevant placeholder, which is
what it is supposed to do. But the ``trace`` message is printed during
the execution, providing us with a glimpse of its inner workings. We can
actually trace value of any type that Lean can coerce to a string
output, and we will see that this includes a number of useful types.

Another thing we can do is trace the current tactic state:

.. code-block:: text

   example : a → b → a ∧ b :=
   by do trace "Hi, Mom!",
         trace_state

Now the output includes the list of *goals* that are active in the
tactic state, each with a local context that includes the local
variables and hypotheses. In this case there is only one:

.. code-block:: text

   Hi, Mom!
   a b : Prop
   ⊢ a → b → a ∧ b

This points to an important fact: the internal, and somewhat mysterious,
tactic state includes at least a list of goals. In fact, it includes
much more: every tactic is invoked in a rich *environment* that includes
all the objects and declarations that are present when the tactic is
invoked, as well as notations, option declarations, and so on. In most
cases, however, the list of goals is most directly relevant to the task
at hand.

Let us dispense with the trace messages now, and start to prove the
theorem by introducing the first two hypotheses.

.. code-block:: text

   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         skip

The backticks indicate that ``h1`` and ``h2`` are *names*; we will
discuss these below. The tactic ``skip`` is a do-nothing tactic, simply
included to ensure that the resulting expression has type
``tactic unit``.

We can now do some looking around. The ``meta_constant`` called
``target`` has type ``tactic expr``, and returns the type of the goal.
The type ``expr``, like ``name``, will be discussed below; it is
designed to reflect the internal representation of Lean expressions, so,
roughly, via meta-programming glue, the ``expr`` type allows us to
manipulate Lean expressions in Lean itself. In particular, we can ask
the tactic to print the current goal:

.. code-block:: text

   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         target >>= trace

In this case, the output is ``a ∧ b``, as we would expect. We can also
ask the tactic to print the elements of the local context.

.. code-block:: text

   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         local_context >>= trace

This yields the list ``[a, b, h1, h2]``. We already happen to have
representations of ``h1`` and ``h2``, because they were returned by the
``intro`` tactic. But we can extract the other expressions in the local
context given their names:

.. code-block:: text

   example : a → b → a ∧ b :=
   by do intro `h1,
         intro `h2,
         ea ← get_local `a,
         eb ← get_local `b,
         trace (to_string ea ++ ", " ++ to_string eb),
         skip

Notice that ``ea`` and ``eb`` are different from ``a`` and ``b``; they
have type ``expr`` rather than ``Prop``. They are the internal
representations of the latter expressions. At present, there is not much
for us to do with these expressions other than print them out, so we
will drop them for now.

In any case, to prove the goal, we can proceed to invoke any of the
Lean's standard tactics. For example, this will work:

.. code-block:: lean

   open tactic

   variables a b : Prop

   -- BEGIN
   example : a → b → a ∧ b :=
   by do intro `h1,
         intro `h2,
         split,
         repeat assumption
   -- END

We can also do it in a more hands-on way:

.. code-block:: lean

   open tactic

   variables a b : Prop

   -- BEGIN
   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         mk_const ``and.intro >>= apply,
         exact eh1,
         exact eh2
   -- END

The double-backticks will also be explained below, but the general idea
is that the third line of the tactic builds an ``expr`` that reflects
the ``and.intro`` declaration in the Lean environment, and applies it.
The ``applyc`` tactic combines these two steps:

.. code-block:: lean

   open tactic

   variables a b : Prop

   -- BEGIN
   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         applyc ``and.intro,
         exact eh1,
         exact eh2
   -- END

We can also finish the proof as follows:

.. code-block:: lean

   open tactic

   variables a b : Prop

   -- BEGIN
   example : a → b → a ∧ b :=
   by do eh1 ← intro `h1,
         eh2 ← intro `h2,
         e ← to_expr ```(and.intro h1 h2),
         exact e
   -- END

Here, the construct :literal:`\```(...)` is used to build a
*pre-expression*, the tactic ``to_expr`` elaborates it and converts it
to an expression, and the ``exact`` tactic applies it. In the next
section, we will see even more variations on constructions like these,
including tactics that would enable us to construct the expression
``and.intro h1 h2`` more explicitly.

The ``do`` block in this example has type ``tactic unit``, and can be
broken out as an independent tactic.

.. code-block:: lean

   open tactic

   variables a b : Prop

   -- BEGIN
   meta def my_tactic : tactic unit :=
   do eh1 ← intro `h1,
      eh2 ← intro `h2,
      e ← to_expr ``(and.intro %%eh1 %%eh2),
      exact e

   example : a → b → a ∧ b :=
   by my_tactic
   -- END

Of course, ``my_tactic`` is not a very exciting tactic; we designed it
to prove one particular theorem, and it will only work on examples that
have the very same shape. But we can write more intelligent tactics that
inspect the goal, the local hypotheses, and the environment, and then do
more useful things. The mechanism is exactly the same: we construct an
expression of type ``tactic unit``, and ask the virtual machine to
execute it at elaboration time to solve the goal at hand.

Names and Expressions
---------------------

Suppose we write an ordinary tactic proof in Lean:

.. code-block:: text

   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   begin
     split,
     exact and.right h,
     exact and.left h
   end

This way of writing the tactic proof suggests that the ``h`` in the
tactic block refers to the expression ``h : a ∧ b`` in the list of
hypotheses. But this is an illusion; what ``h`` *really* refers to is
the first hypothesis *named* ``h`` that is in the local context of the
goal in the state when the tactic is executed. This is made clear, for
example, by the fact that earlier lines in the proof can change the name
of the hypothesis:

.. code-block:: text

   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   begin
     revert h,
     intro h',
     split,
     exact and.right h',
     exact and.left h'
   end

Now writing ``exact and.right h`` would make no sense. We could,
alternatively, contrive to make ``h`` denote something different from
the original hypothesis. This often happens with the ``cases`` and
``induction`` tactics, which revert hypotheses, peform an action, and
then reintroduce new hypotheses with the same names.

Metaprogramming in Lean requires us to be mindful of and explicit about
the distinction between expressions in the current environment, like
``h : a ∧ b`` in the hypothesis of the example, and the Lean objects
that we use to act on the tactic state, such as the name "h" or an
object of type ``expr``. Without using the ``begin...end`` front end, we
can construct the proof as follows:

.. code-block:: text

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
      to_expr ```(and.right h) >>= exact,
      to_expr ```(and.left h) >>= exact
   -- END

This tells Lean to elaborate the expressions ``and.right h`` and
``and.left h`` in the context of the current goal, and then apply them.
The ``begin...end`` construct is essentially a front end that interprets
the proof above in these terms.

To understand what is going on in situations like this, it is important
to know that Lean's metaprogramming framework provides three distinct
Lean types that are relevant to constructing syntactic expressions:

-  the type ``name``, representing *hierarchical names*
-  the type ``expr``, representing *expressions*
-  the type ``pexpr``, representing *pre-expressions*

Let us consider each one of them, in turn.

Hierarchical names are denoted in ordinary .lean files with expressions
like ``foo.bar.baz`` or ``nat.mul_comm``. They are used as identifiers
that reference defined constants in Lean, but also for local variables,
attributes, and other objects. Their Lean representations are defined in
``init/meta/name.lean``, together with some operations that can be
performed on them. But for many purposes we can be oblivious to the
details. Whenever we type an expression that begins with a backtick that
is not followed by an open parenthesis, Lean's parser translates this to
the construction of the associated name. In other words,
:literal:`\`nat.mul_comm` is simply notation for the compound name with
components ``nat`` and ``mul_comm``.

When metaprogramming, we often use names to refer to definitions and
theorems in the Lean environment. In situations like that, it is easy to
make mistakes. In the example below, the tactic definition is accepted,
but its application fails:

.. code-block:: lean

   open tactic

   namespace foo

   theorem bar : true := trivial

   meta def my_tac : tactic unit :=
   mk_const `bar >>= exact

   -- example : true := by my_tac -- fails

   end foo

The problem is that the proper name for the theorem is ``foo.bar``
rather than ``bar``; if we replace :literal:`\`bar` by
:literal:`\`foo.bar`, the example is accepted. The ``mk_const`` tactic
takes an arbitrary name and attempts to resolve it when the tactic is
invoked, so there is no error in the definition of the tactic. The error
is rather that when we wrote :literal:`\`bar` we had in mind a
particular theorem in the environment at the time, but we did not
identify it correctly.

For situations like these, Lean provides double-backtick notation. The
following example succeeds:

.. code-block:: lean

   open tactic

   namespace foo

   theorem bar : true := trivial

   meta def my_tac : tactic unit :=
   mk_const ``bar >>= exact

   example : true := by my_tac -- fails

   end foo

It also succeeds if we replace :literal:`\``bar` by
:literal:`\``foo.bar`. The double-backtick asks the parser to resolve
the expression with the name of an object in the environment *at parse
time*, and insert the relevant name. This has two advantages:

-  if there is no such object in the environment at the time, the parser
   raises an error; and
-  assuming it does find the relevant object in the environment, it
   inserts the full name of the object, meaning we can use abbreviations
   that make sense in the context where we are writing the tactic.

As a result, it is a good idea to use double-backticks whenever you want
to refer to an existing definition or theorem.

When writing tactics, it is often necessary to generate a fresh name.
You can use ``mk_fresh_name`` for that:

.. code-block:: lean

   open tactic

   -- BEGIN
   example (a : Prop) : a → a :=
   by do n ← mk_fresh_name,
         intro n,
         hyp ← get_local n,
         exact hyp
   -- END

The type ``expr`` reflects the internal representation of Lean
expressions. It is defined inductively in the file ``expr.lean``, but
when evaluating expressions that involve terms of type ``expr``, the
virtual machine uses the internal C++ representations, so each
constructor and the eliminator for the type are translated to the
corresponding C++ functions. Expressions include the sorts ``Prop``,
``Type₁``, ``Type₂``, …, constants of each type, applications, lambdas,
Pi types, and let definitions. The also include de Bruijn indices (with
constructor ``var``), metavariables, local constants, and macros.

The whole purpose of tactic mode is to construct expressions, and so
this data type is fundamental. We have already seen that the ``target``
tactic returns the current goal, which is an expression, and that
``local_context`` returns the list of hypotheses that can be used to
solve the current goal, that is, a list of expressions.

Returning to the example at the start of this section, let us consider
ways of constructing the expressions ``and.left h`` and ``and.right h``
more explicitly. The following example uses the ``mk_mapp`` tactic.

.. code-block:: lean

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
      eh ← get_local `h,
      mk_mapp ``and.right [none, none, some eh] >>= exact,
      mk_mapp ``and.left [none, none, some eh] >>= exact
   -- END

In this example, the invocations of ``mk_mapp`` retrieve the definition
of ``and.right`` and ``and.left``, respectively. It makes no difference
whether the arguments to those theorems have been marked implicit or
explicit; ``mk_mapp`` ignores those annotations, and simply applies that
theorem to all the arguments in the subsequent list. Thus the first
argument to ``mk_mapp`` is a name, while the second argument has type
``list (option expr)``. Each ``none`` entry in the list tells
``mk_mapp`` to treat that argument as implicit and infer it using type
inference. In contrast, an entry of the form ``some t`` specifies ``t``
as the corresponding argument.

The tactic ``mk_app`` is an even more rudimentary application builder.
It takes the name of the operator, followed by a complete list of its
arguments.

.. code-block:: lean

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
         ea ← get_local `a,
         eb ← get_local `b,
         eh ← get_local `h,
         mk_app ``and.right [ea, eb, eh] >>= exact,
         mk_app ``and.left [ea, eb, eh] >>= exact
   -- END

You can send less than the full list of arguments to ``mk_app``, but the
arguments you send are assumed to be the *final* arguments, with the
earlier ones made implicit. Thus, in the example above, we could send
instead ``[eb, eh]`` or simply ``[eh]``, because the earlier arguments
can be inferred from these.

.. code-block:: lean

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
         eh ← get_local `h,
         mk_app ``and.right [eh] >>= exact,
         mk_app ``and.left [eh] >>= exact
   -- END

Finally, as indicated in the last section, you can also use ``mk_const``
to construct a constant expression from the corresponding name:

.. code-block:: lean

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
         eh ← get_local `h,
         mk_const ``and.right >>= apply,
         exact eh,
         mk_const ``and.left >>= apply,
         exact eh
   -- END

We have also seen above that it is possible to use ``to_expr`` to
elaborate expressions at executation time, in the context of the current
goal.

.. code-block:: text

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
      to_expr ```(and.right h) >>= exact,
      to_expr ```(and.left h) >>= exact
   -- END

Here, the expressions :literal:`\```(and.right h)` and
:literal:`\```(and.left h)` are pre-expressions, that is, objects of
type ``pexpr``. The interface to ``pexpr`` can be found in the file
``pexpr.lean``, but the type is largely opaque from within Lean. The
canonical use is given by the example above: when Lean's parser
encounters an expression of the form :literal:`\```(...)`, it constructs
the corresponding ``pexpr``, which is simply an internal representation
of the unelaborated term. The ``to_expr`` tactic then sends that object
to the elaborator when the tactic is executed.

Note that the backtick is used in two distinct ways: an expression of
the form :literal:`\`n`, without the parentheses, denotes a ``name``,
whereas an expression of the form :literal:`\`(...)`, with parentheses,
denotes a ``pexpr``. Though this may be confusing at first, it is easy
to get used to the distinction, and the notation is quite convenient.

Lean's pre-expression mechanism also supports the use of
*anti-quotation*, which allows a tactic to tell the elaborator to insert
an expression into a pre-expression at runtime. Returning to the example
above, suppose we are in a situation where instead of the name ``h``, we
have the corresponding *expression*, ``eh``, and want to use that to
construct the term. We can insert it into the pre-expression by
preceding it with a double-percent sign:

.. code-block:: text

   open tactic

   -- BEGIN
   example (a b : Prop) (h : a ∧ b) : b ∧ a :=
   by do split,
      eh ← get_local `h,
      to_expr ``(and.right %%eh) >>= exact,
      to_expr ``(and.left %%eh) >>= exact
   -- END

When the tactic is executed, Lean elaborates the pre-expressions given
by :literal:`\``(...)`, with the expression ``eh`` inserted in the right
place. The difference between :literal:`\``(...)` and
:literal:`\```(...)` is that the first resolves the names contained in
the expression when the tactic is defined, whereas the second resolves
them when the tactic is executed. Since the only name occurring in
``and.left %%eh`` is ``and.left``, it is better to resolve it right
away. However, in the expression ``and.right h`` above, ``h`` only comes
into existence when the tatic is executed, and so we need to use the
triple backtick.

[TODO: describe :literal:`\`(...)`, and improve the explanations]

Examples
--------

When it comes to writing tactics, you have all the computable entities
of Lean's standard library at your disposal, including lists, natural
numbers, strings, product types, and so on. This makes the tactic monad
a powerful mechanism for writing metaprograms. Some of Lean's most basic
tactics are implemented internally in C++, but many of them are defined
from these in Lean itself.

The entry point for the tactic library is the file
``init/meta/tactic.lean``, where you can find the details of the
interface, and see a number of basic tactics implemented in Lean. For
example, here is the definition of the ``assumption`` tactic:

.. code-block:: lean

   open tactic
   namespace hide

   -- BEGIN
   meta def find_same_type : expr → list expr → tactic expr
   | e []         := failed
   | e (h :: hs) :=
     do t ← infer_type h,
        (unify e t >> return h) <|> find_same_type e hs

   meta def assumption : tactic unit :=
   do ctx ← local_context,
      t   ← target,
      h   ← find_same_type t ctx,
      exact h
   <|> fail "assumption tactic failed"
   -- END
   end hide

The expression ``find_same_type t es`` tries to find in ``es`` an
expression with type definitionally equal to ``t`` in the list of
expressions ``es``, by a straightforward recursion on the list. The
``infer_type`` tactic calls Lean's internal type inference mechanism to
infer to the type of an expression, and the ``unify`` tactic (which will
be discussed further in Section `Section
8.6 <#Metavariables_and_Unification>`__ tries to unify two expressions,
instantiating metavariables if necessary. Note the use of the ``orelse``
notation: if the unification fails, the procedure backtracks and
continues to try the remaining elements on the list. The ``fail`` tactic
announces failure with a given string. The ``failed`` tactic simply
fails with a generic message, "tactic failed."

One can even manipulate data structures that include tactics themselves.
For example, the ``first`` tactic takes a list of tactics, and applies
the first one that succeeds:

.. code-block:: lean

   open tactic

   -- BEGIN
   meta def first {α : Type} : list (tactic α) → tactic α
   | []      := fail "first tactic failed, no more alternatives"
   | (t::ts) := t <|> first ts
   -- END

It fails if none of the tactics on the list succeeds. Consider the
example from `Section
1.4 <01_Introduction.org::#Metaprogramming_in_Lean>`__ of the
Introduction:

.. code-block:: lean

   open tactic monad expr

   -- BEGIN
   meta def destruct_conjunctions : tactic unit :=
   repeat (do
     l ← local_context,
     first $ l.map (λ h, do
       ht ← infer_type h >>= whnf,
       match ht with
       | `(and %%a %%b) := do
         n ← get_unused_name `h none,
         mk_mapp ``and.left [none, none, some h] >>= assertv n a,
         n ← get_unused_name `h none,
         mk_mapp ``and.right [none, none, some h] >>= assertv n b,
         clear h
       | _ := failed
       end))
   -- END

The ``repeat`` tactic simply repeats the inner block until it fails. The
inner block starts by getting the local context. The expression
``l.map ...`` is just shorthand for ``list.map ... l``; it applies the
function in ``...`` to each element of ``l`` and returns the resulting
list, in this case a list of tactics. The ``first`` function then calls
each one sequentially until one of them succeeds. Note the use of the
dollar-sign for function application. In general, an expression ``f $
a`` denotes nothing more than ``f a``, but the binding strength is such
that you do not need to use extra parentheses when ``a`` is a long
expression. This provides a convenient idiom in situations exactly like
the one in the example.

Some of the elements of the body of the main loop will now be familiar.
For each element ``h`` of the context, we infer the type of ``h``, and
reduce it to weak head normal form. (We will discuss weak head normal
form in the next section.) Assuming the type is an ``and``, we construct
the terms ``and.left h`` and ``and.right h`` and add them to the context
with a fresh name. The ``clear`` tactic then deletes ``h`` itself.

Remember that when writing ``meta defs`` you can carry out arbitrary
recursive calls, without any guarantee of termination. You should use
this with caution when writing tactics; if there is any chance that some
unforseen circumstance will result in an infinite loop, it is wiser to
use a large cutoff to prevent the tactic from hanging. Even the
``repeat`` tactic is implemented as a finite iteration:

.. code-block:: lean

   open tactic nat
   namespace hide

   -- BEGIN
   meta def repeat_at_most : nat → tactic unit → tactic unit
   | 0        t := skip
   | (succ n) t := (do t, repeat_at_most n t) <|> skip

   meta def repeat : tactic unit → tactic unit :=
   repeat_at_most 100000
   -- END

   end hide

But 100,000 iterations is still enough to get you into trouble if you
are not careful.

Reduction
---------

[This section still under construction. It will discuss the various
types of reduction, the notion of weak head normal form, and the various
transparency settings. It will use some of the examples that follow.]

.. code-block:: lean

   open tactic

   set_option pp.beta false

   section
     variables {α : Type} (a b : α)

     example : (λ x : α, a) b = a :=
     by do goal ← target,
           match expr.is_eq goal with
           | (some (e₁, e₂)) := do trace e₁,
                                   whnf e₁ >>= trace,
                                   reflexivity
           | none            := failed
           end

     example : (λ x : α, a) b = a :=
     by do goal ← target,
           match expr.is_eq goal with
           | (some (e₁, e₂)) := do trace e₁,
                                   whnf e₁ transparency.none >>= trace,
                                   reflexivity
           | none            := failed
           end

     attribute [reducible]
     definition foo (a b : α) : α := a

     example : foo a b = a :=
     by do goal ← target,
           match expr.is_eq goal with
           | (some (e₁, e₂)) := do trace e₁,
                                   whnf e₁ transparency.none >>= trace,
                                   reflexivity
           | none            := failed
           end

     example : foo a b = a :=
     by do goal ← target,
           match expr.is_eq goal with
           | (some (e₁, e₂)) := do trace e₁,
                                   whnf e₁ transparency.reducible >>= trace,
                                   reflexivity
           | none            := failed
           end
   end

.. _Metavariables_and_Unification:

Metavariables and Unification
-----------------------------

[This section is still under construction. It will discuss the notion of
a metavariable and its local context, with the interesting bit of
information that goals in the tactic state are nothing more than
metavariables. So the goal list is really just a list of metavariables,
which can help us make sense of the ``get_goals`` and ``set_goals``
tactics. It will also discuss the ``unify`` tactic.]
