.. _Introduction:

Introduction
============

*Warning.* This book is still under construction. It aims to serve as
both an introduction and a reference manual for programming in the Lean
theorem prover.

We are making this material public now because currently it is the only
existing documentation for many of the specifics of the Lean programming
language and its API, and we are hoping that the information will be
useful to brave souls experimenting with it at this early stage. Most of
the chapters are currently only stubs, but comments and feedback on the
material that is available will be helpful.

Lean as a Programming Language
------------------------------

This book can be viewed as a companion to `Theorem Proving in
Lean <https://leanprover.github.io/theorem_proving_in_lean/>`__, which
presents Lean as a system for building mathematical libraries and
stating and proving mathematical theorems. From that perspective, the
point of Lean is to implement a formal axiomatic framework in which one
can define mathematical objects and reason about them.

As noted in that book, however, expressions in Lean have a computational
interpretation, which is to say, they can be *evaluated*. As long as it
is defined in the computational fragment of Lean's foundational
language, any closed term of type ``nat`` – that is, any term of type
``nat`` without free variables – evaluates to a numeral. Similarly, any
closed term of type ``list nat`` evaluates to a list of numerals, and
any closed term of type ``bool`` evaluates either to the boolean value
``tt``, for "true," or ``ff``, for "false."

This provides another perspective on Lean: instead of thinking of it as
a theorem prover whose language just happens to have a computational
interpretation, think of it as a programming language that just happens
to come equipped with a rich specification language and an interactive
environment for proving that programs meet their specifications. The
specification language and proof system are quite powerful, rich enough,
in fact, to include all conventional mathematics.

We will see that Lean's underlying logical framework, the Calculus of
Inductive Constructions, constitutes a surprisingly good programming
language. It is expressive enough to define all sorts of data
structures, and it supports powerful abstractions. Programs written in
the language can be evaluated efficiently by Lean's virtual-machine
interpreter or translated automatically to C++ and compiled.

Viewed from a computational perspective, the Calculus of Inductive
Constructions is an instance of a purely functional programming
language. This means that a program in Lean is simply an expression
whose value is determined compositionally from the values of the other
expressions it refers to, independent of any sort of ambient state of
computation. There is no notion of storing a result in memory or
changing the value of a global variable; computation is just evaluation
of expressions. This paradigm makes it easier to reason about programs
and verify their correctness. At the same time, we will see that Lean
incorporates concepts and abstractions that make it feasible to use this
paradigm in practice.

The underlying foundational framework imposes one restriction that is
alien to most programming languages, namely, that every program is
terminating. So, for example, every "while" loop has to be explicitly
bounded, though, of course, we can consider the result of iterating an
arbitrary computation ``n`` times for any given natural number ``n``. We
will see that Lean provides flexible mechanisms for structural and
well-founded recursion, allowing us to define functions in natural ways.
At the same, the system provides complementary mechanisms for proving
claims, using inductive principles that capture the structure of the
function definitions.

Examples
--------

For example…

[Define something like factorial. Evaluate (use both ``reduce`` and
``eval``).]

[Define operations on lists.]

[Prove things, like ``length (reverse l) = length l`` or ``reverse
(reverse l) = l``.]

Input and Output
----------------

People often want to write programs that interact with the outside
world, querying users for input and presenting them with output during
the course of a computation. Lean's foundational framework has no model
of "the real world," but Lean declares ``get_str`` and ``put_str``
commands to get an input string from the user and write an input string
to output, respectively. Within the foundational system, these are
treated as black box operations. But when programs are evaluated by
Lean's virtual machine or when they are translated to C++, they have the
expected behavior. Here, for example, is a program that prints "hello
world":

.. code-block:: lean

   import system.io
   variable [io.interface]
   open io

   def hello_world : io unit :=
   put_str "hello world\n"

   #eval hello_world

The next example prints the first 100 squares:

.. code-block:: lean

   import system.io
   variable [io.interface]
   open nat io

   def print_squares : ℕ → io unit
   | 0        := return ()
   | (succ n) := print_squares n >>
                 put_str (nat.to_string n ++ "^2 = " ++ 
                          nat.to_string (n * n) ++ "\n")

   #eval print_squares 100

We will explain the data type ``io unit`` in Chapter
`Monads <07_Monads::#Monads>`__. Although this program has a real world
side effect of sending output to the screen when run, that effect is
invisible to the formal foundation. From the latter's perspective, the
type constructor ``io`` and the functions ``put_str`` and ``get_str``
are entirely opaque, objects about which that the axiomatic system has
nothing to say. The ``print
axioms`` command shows that the expression ``hello world`` depends on
the constants ``io`` and ``put_str``, which have been forcibly added to
the axiomatic system.

.. code-block:: lean

   import system.io
   variable [io.interface]
   open io

   def hello_world : io unit :=
   put_str "hello world\n"

   -- BEGIN
   #print axioms hello_world
   -- END

In this way, we can prove properties of programs involving ``io`` that
do not depend in any way on the particular results of the input and
output.

.. _Metaprogramming_in_Lean:

Metaprogramming in Lean
-----------------------

Lean also allows *metaprograms*, which are Lean programs that involve
objects and constructs that are not part of the axiomatic foundation. In
particular:

-  Metaprograms can use arbitrary recursive calls, with no concern for
   termination.
-  Metaprograms can access *metaconstants*, that is, primitive functions
   and objects that are implemented internally in Lean and are not meant
   to be trusted by the foundational framework.

Such definitions can be introduced using the keywords ``meta def``
instead of ``def`` and are marked for special treatment. In particular,
because they are not part of the axiomatic foundation, they cannot
appear as part of ordinary Lean definitions and theorems.

For example, the following definition computes McCarthy's 91 function,
without verifying that the computation terminates on all inputs (though,
in fact, it does):

.. code-block:: lean

   meta def m91 : ℕ → ℕ
   | n := if n > 100 then n - 10 else m91 (m91 (n + 11))

   #eval m91 10
   #eval m91 100
   #eval m91 1000

We can print out the first 120 values of ``m91``:

.. code-block:: lean

   import system.io
   variable [io.interface]
   open nat io

   meta def m91 : ℕ → ℕ
   | n := if n > 100 then n - 10 else m91 (m91 (n + 11))

   -- BEGIN
   meta def print_m91 : ℕ → io unit
   | 0        := return ()
   | (succ n) := print_m91 n >>
                 put_str ("m91 " ++ nat.to_string n ++ " = " ++ 
                          nat.to_string (m91 n) ++ "\n")

   #eval print_m91 120
   -- END

Of course, such uses of recursion are dangerous.

.. code-block:: lean

   meta def foo : ℕ → ℕ
   | n := foo n + 1

   #reduce foo
   -- #eval foo 0

Evaluating ``foo`` using the kernel evaluator shows that the
implementation is a bit of a hack; the term in the definition includes a
macro which names ``foo`` itself. The virtual machine that evaluates foo
goes further, and carries out the recursive call, repeating this until
the process runs out of memory. It is a good thing that Lean will not
allow ``foo`` to appear in a ``theorem`` or in an ordinary
``definition``; if we could prove ``foo = foo + 1`` then, substracting
``foo`` from both sides, we could prove ``0 = 1``, and hence a
contradiction.

Although metaprograms can be used in various ways, its primary purpose
is to provide a means of extending the functionality of Lean, within
Lean itself. For example, we can use metaprograms to write new
procedures, known as *tactics*, which help us construct proofs. This
next example assumes you are familiar with the notion of a tactic, as
described in *Theorem Proving in Lean*.

The following code implements a tactic that, given any goal, repeatedly
finds a hypothesis ``h`` of the form ``a ∧ b``, and replaces it by
hypotheses (with fresh names) for ``a`` and ``b``.

.. code-block:: lean

   open tactic monad expr

   -- BEGIN
   meta def destruct_conjunctions : tactic unit :=
   repeat (do
     l ← local_context,
     first $ l^.for (λ h, do
       ht ← infer_type h >>= whnf,
       match ht with
       | `(and %%a %%b) := do
         n ← mk_fresh_name,
         mk_mapp ``and.left [none, none, some h] >>= assertv n a,
         n ← mk_fresh_name,
         mk_mapp ``and.right [none, none, some h] >>= assertv n b,
         clear h
       | _ := failed
       end))
   -- END

We will explain the details in `Chapter
8 <08_Writing_Tactics.org::#Writing_Tactics>`__ but, roughly speaking,
the code repeats the following action until there is nothing left to do:
get the list of hypotheses in the local context, find a hypothesis ``h``
whose type is a conjunction, add new hypotheses justified by ``and.left
h`` and ``and.right h`` to the local context, and then delete ``h``. We
can then use ``destruct_conjunctions`` like any other Lean tactic.

.. code-block:: lean

   open tactic monad expr

   meta def destruct_conjunctions : tactic unit :=
   repeat (do
     l ← local_context,
     first $ l^.for (λ h, do
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

   -- BEGIN
   example (a b c : Prop) (h : (a ∧ b) ∧ (c ∧ a)) : c :=
   begin destruct_conjunctions >> assumption end
   -- END

Note that the reason we can use such code to prove theorems without
compromising the integrity of the formal system is that Lean's kernel
always certifies the result. From a foundational point of view, we don't
have to worry about the integrity of the code, only the integrity of the
resulting proofs.

Overview of the contents
------------------------

To summarize, we can use Lean in any of the following ways:

-  as a programming language
-  as a system for verifying properties of programs
-  as a system for writing metaprograms, that is, programs that extend
   the functionality of Lean itself

Chapters `2 <02_Programming_Basics.org::#Programming_Basics>`__ to
`7 <07_Monads.org::#Monads>`__ explain how to use Lean as a programming
language. It will be helpful if you have some familiarity with the
syntax and meaning of dependent type theory, for example, as presented
in *Theorem Proving in Lean* (henceforth *TPL*). But, if not, it is
likely that you will be able to pick up the details as we proceed.
Similarly, if you are familiar with functional programming, you will be
able to move through the material more quickly, but we will try to keep
the presentation below self contained.

`Chapter
4 <04_Verifying_Properties_of_Programs.org::#Verifying_Properties_of_Programs>`__
in particular deals with the task of proving things about programs. Once
again, it will be helpful if you are familiar with the use of Lean as an
interactive theorem prover as described in *TPL*, but if not you are
encouraged to forge ahead and refer back to *TPL* as necessary.

Finally, `Chapter 8 <08_Writing_Tactics.org::#Writing_Tactics>`__ and
`Chapter 9 <09_Writing_Automation.org::#Writing_Automation>`__ deal with
metaprogramming aspects of Lean, and, in particular, writing tactics and
automation.
