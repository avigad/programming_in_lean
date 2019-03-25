.. _Basic_Programming:

Basic Programming
=================

This chapter introduces the basics of using Lean as a programming language. It is not a proper introduction to programming, however. There are a number of good introductions to functional programming, including `Learn You a Haskell for Great Good <https://leanprover.github.io/theorem_proving_in_lean/>`__. If functional programming is new to you, you might find it helpful to read another text and port the examples and exercises to Lean.

Evaluating Expressions
----------------------

When translating expressions to byte code, Lean's virtual machine evaluator ignores type information entirely. The whole elaborate typing schema of the CIC serves to ensure that terms make sense, and mean what we think they mean. Type checking is entirely static: when evaluating a term ``t`` of type ``α``, the bytecode evaluator ignores ``α``, and simply computes the value of ``t``, as described below. As noted above, any subexpressions of ``t`` whose type is an element of ``Prop`` are computationally irrelevant, and they are ignored too.

The evaluation of expressions follows the computational rules of the CIC. In particular:

-  To evaluate a function application ``(λ x, s) t``, the bytecode evaluator evaluates ``t``, and then evaluates ``s`` with ``x`` instantiated to ``t``.
-  To evaluate an eliminator for an inductively defined type — in other words, a function defined by pattern matching or recursion — the bytecode evaluator waits until all the arguments are given, evaluates the first one, and, on the basis of the result, applies the relevant case or recursive call.

The evaluation strategy for function application is known as *eager evaluation*: when applying a function ``f`` to as sequence of arguments ``t1`` ... ``tn``, the arguments are evaluated first, and then the body of the function is evaluated with the results.

We have already seen that Lean can evaluate expressions involving natural numbers, integers, lists, and booleans.

.. code-block:: lean

   #eval 22 + 77 * 11
   #eval tt && (ff || tt)
   #eval [1, 2, 3] ++ 4 :: [5, 6, 7]

Lean can evaluate conditional expressions:

.. code-block:: lean

   #eval if 11 > 5 ∧ ff then 27 else 33 + 12

   #eval if 7 ∈ [1, 3, 5] then "hooray!" else "awww..."

Here is a more interesting example:

.. code-block:: lean

   def craps (roll : ℕ) (come_out : bool) (point : ℕ) : string :=
   if (come_out ∧ (roll = 7 ∨ roll = 11)) ∨ (¬ come_out ∧ roll = point) then
     "You win!"
   else if (come_out ∧ roll ∈ [2, 3, 12]) ∨ (¬ come_out ∧ roll = 7) then
     "You lose!"
   else
     "Roll again."

   #eval craps 7 tt 4
   #eval craps 11 ff 2

The standard library defines a number of common operations on lists:

.. code-block:: lean

   #eval list.range 100

   #eval list.map (λ x, x * x) (list.range 100)

   #eval list.filter (λ x, x > 50) (list.range 100)

   #eval list.foldl (+) 0 (list.range 100)

A ``char`` is a natural number that is less than 255. You can enter the character "A," for example, by typing ``'A'``. Lean defines some basic operations on characters:

.. code-block:: lean

   open char

   #eval to_lower 'X'
   #eval to_lower 'x'
   #eval to_lower '!'

   #eval to_lower '!'

   #eval if is_punctuation '?' then tt else ff

In the example above, we have to tell Lean how to define a decision procedure for the predicate ``is_punctuation``. We do this simply by unfolding the definition and asking Lean to use the inferred decision procedure for list membership.

Strings can be mapped to lists of characters and back, so operations on lists and be used with strings.

.. code-block:: lean

   namespace string

   def filter (p : char → Prop) [decidable_pred p] (s : string) : string :=
   ((s.to_list).filter p).as_string

   def map (f : char → char) (l : string) : string :=
   (l.to_list.map f).as_string

   def to_lower (s : string) : string := s.map char.to_lower

   def reverse (s : string) : string := s.to_list.reverse.as_string

   def remove_punctuation (s : string) : string :=
   s.filter (λ c, ¬ char.is_punctuation c)

   end string

We can use these to write a procedure that tests to see whether a given sentence is a palindrome.

.. code-block:: lean

   namespace string

   def filter (p : char → Prop) [decidable_pred p] (s : string) : string :=
   ((s.to_list).filter p).as_string

   def map (f : char → char) (l : string) : string :=
   (l.to_list.map f).as_string

   def to_lower (s : string) : string := s.map char.to_lower

   def reverse (s : string) : string := s.to_list.reverse.as_string

   def remove_punctuation (s : string) : string :=
   s.filter (λ c, ¬ char.is_punctuation c)

   -- BEGIN
   def test_palindrome (s : string) : bool :=
   let s' := to_lower (remove_punctuation s) in
   if s' = reverse s' then tt else ff

   #eval test_palindrome "A man, a plan, a canal -- Panama!"
   #eval test_palindrome "Madam, I'm Adam!"
   #eval test_palindrome "This one is not even close."
   -- END

   end string

.. _Recursive_Definitions:

Recursive Definitions
---------------------

Lean supports definition of functions by structural recursion on its arguments.

.. code-block:: lean

   open nat

   def fact : ℕ → ℕ
   | 0        := 1
   | (succ n) := (succ n) * fact n

   #eval fact 100

Lean recognizes that addition on the natural numbers is defined in terms of the ``succ`` constructor, so you can also use more conventional mathematical notation.

.. code-block:: lean

   def fact : ℕ → ℕ
   | 0     := 1
   | (n+1) := (n+1) * fact n

Lean will compile definitions like these down to the primitives of the Calculus of Inductive Constructions, though in the case of ``fact`` it is straightforward to define it from the primitive recursion principle directly.

Lean's function definition system can handle more elaborate forms of pattern matching with defaults. For example, the following function returns true if and only if one of its arguments is positive.

.. code-block:: lean

   def foo : ℕ → ℕ → ℕ → bool
   | (n+1) _      _     := tt
   | _     (m+1)  _     := tt
   | _      _     (k+1) := tt
   | _      _        _  := ff

We can define the sequence of Fibonacci numbers in a natural way:

.. code-block:: lean

   def fib : ℕ → ℕ
   | 0     := 1
   | 1     := 1
   | (n+2) := fib (n+1) + fib n

   #eval fib 10

When evaluating ``fib``, the virtual machine uses the defining equations. As a result, this naive implementation runs in exponential time, since the computation of ``fib (n+2)`` calls for two independent computations of ``fib n``, one hidden in the computation of ``fib (n+1)``. The following more efficient version defines an auxiliary function that computes the values in pairs:

.. code-block:: lean

   def fib_aux : ℕ → ℕ × ℕ
   | 0     := (0, 1)
   | (n+1) := let p := fib_aux n in (p.snd, p.fst + p.snd)

   def fib n := (fib_aux n).snd

   #eval fib 1000

A similar solution is to use additional arguments to accumulate partial results:

.. code-block:: lean

   def fib_aux : ℕ → ℕ → ℕ → ℕ
   | 0     a b := b
   | (n+1) a b := fib_aux n b (a+b)

   def fib n := fib_aux n 0 1

   #eval fib 1000

Functions on lists are naturally defined by structural recursion. These definitions are taken from the standard library:

.. code-block:: lean

   namespace hidden
   open list

   -- BEGIN
   universe u
   variable {α : Type u}

   def append : list α → list α → list α
   | []       l := l
   | (h :: s) t := h :: (append s t)

   def mem : α → list α → Prop
   | a []       := false
   | a (b :: l) := a = b ∨ mem a l

   def concat : list α → α → list α
   | []     a := [a]
   | (b::l) a := b :: concat l a

   def length : list α → nat
   | []       := 0
   | (a :: l) := length l + 1

   def empty : list α → bool
   | []       := tt
   | (_ :: _) := ff

   -- END
   end hidden

Notice that ``mem`` defines a predicate on lists, which is to say, ``mem a l`` asserts that ``a`` is a member of the list ``l``. To use it computationally, say, in an if-then-else clause, one needs to establish that this instance is decidable, or (what comes to essentially the same thing) define a version that takes values in type ``bool`` instead.

Inhabited Types, Subtypes, and Option Types
-------------------------------------------

In the Calculus of Inductive Constructions, every term denotes something. In particular, if ``f`` has a function type and ``t`` has the corresponding argument type, the ``f t`` denotes some object. In other words, a function defined on a type has to be define on *every* element of that type, so that every function is total on its domain.

It often happens that a function is naturally defined only on some elements of a type. For example, one can take the head of a list only if it is nonempty, and one can divide one rational number or real number by another as long as the second is nonzero. There are a number of ways of handling that in dependent type theory.

The first, and simplest, is to totalize the function, by assigning an arbitrary or conveniently chosen value where the function would otherwise be undefined. For example, it is convenient to take ``x / 0`` to be equal to ``0``. A downside is that this can run counter to mathematical intuitions. But it does give a precise meaning to the division symbol, even if it is a nonconventional one. (The treatment of undefined values in ordinary mathematics is often ambiguous and sloppy anyhow.)

It helps that the Lean standard library defines a type class, ``inhabited α``, that can be used to keep track of types that are known to have at least one element, and to infer such an element. The expressions ``default α`` and ``arbitrary α`` both denote the element that is inferred. The second is unfolded less eagerly by Lean's elaborator, and should be used to indicate that you do not want to make any assumptions about the value returned (though ultimately nothing can stop a theory making use of the fact that the arbitrary element of nat, say, is chosen to be zero). The list library defines the ``head`` function as follows:

.. code-block:: lean

   universe u
   variable {α : Type u}

   def head [inhabited α] : list α → α
   | []       := default α
   | (a :: l) := a

Another possibility is to add a precondition to the function. We can do this because in the CIC, an assertion can be treated as an argument to a function. The following function explicitly requires evidence that the argument ``l`` is not the empty list.

.. code-block:: lean

   universe u
   variable {α : Type u}

   -- BEGIN
   def first : Π (l : list α), l ≠ [] → α
   | []        h := absurd rfl h
   | (a :: l₀) h := a
   -- END

This contract ensures that ``first`` will never be called to evaluate the first element of an empty list. The check is entirely static; the evidence is ignored by the bytecode evaluator.

A closely related solution is to use a ``subtype``. This simply bundles together the data and the precondition.

.. code-block:: lean

   universe u
   variable {α : Type u}

   def first : Π (l : list α), l ≠ [] → α
   | []        h := absurd rfl h
   | (a :: l₀) h := a

   -- BEGIN
   def first' : {l₀ // l₀ ≠ []} → α :=
   λ l, first l.1 l.2
   -- END

Here, the type ``{l₀ // l₀ ≠ []}`` consists of (dependent) pairs, where the first element is a list and the second is evidence that the list is nonempty. In a similar way, ``{n // (n : ℤ) > 0}`` denotes the type of positive integers. Using subtypes and preconditions can be inconvenient at times, because using them requires a mixture of proof and calculation. But subtypes are especially useful when the constraints are common enough that is pays to develop a library of functions that take and return elements satisfying them — in other words, when the subtype is really worthy of being considered a type in its own right.

Yet another solution is to signal the success or failure of the function on the output, using an ``option`` type. This is defined in the standard library as follows:

.. code-block:: lean

   namespace hidden

   universe u

   -- BEGIN
   inductive option (α : Type u)
   | none {} : option
   | some    : α → option
   -- END

   end hidden

You can think of the return value ``none`` as signifying that the function is undefined at that point, whereas ``some a`` denotes a return value of ``a``. (The inscription ``{}`` after the none constructor indicates that the argument ``α`` should be marked implicit, even though it cannot be inferred from other arguments.) For example, then ``nth`` element function is defined in the list library as follows:

.. code-block:: lean

   universe u
   variables {α : Type u} [inhabited α]

   open option nat

   -- BEGIN
   def nth : list α → nat → option α
   | []       n     := none
   | (a :: l) 0     := some a
   | (a :: l) (n+1) := nth l n
   -- END

To use an element ``oa`` of type ``option α``, one typically has to pattern match on the cases ``none`` and ``some α``. Doing this manually in the course of a computation can be tedious, but it is much more pleasant and natural using *monads*, which we turn to next.

Input and Output
----------------

Lean can support programs that interact with the outside  world, querying users for input and presenting them with output during the course of a computation. Lean's foundational framework has no model of "the real world," but Lean declares ``get_str`` and ``put_str`` commands to get an input string from the user and write an input string to output, respectively. Within the foundational system, these are treated as black box operations. But when programs are evaluated by Lean's virtual machine or when they are translated to C++, they have the expected behavior. Here, for example, is a program that prints "hello world":

.. code-block:: lean

    import system.io
    open io

    def hello_world : io unit :=
    put_str "hello world\n"

    #eval hello_world

The next example prints the first 100 squares:

.. code-block:: lean

   import system.io
   open io

   def print_squares : ℕ → io unit
   | 0     := return ()
   | (n+1) := print_squares n >>
              put_str (to_string n ++ "^2 = " ++
                to_string (n * n) ++ "\n")

   #eval print_squares 100

We will explain the data type ``io unit`` in :numref:`Chapter %s <Monads>`. Although this program has a real world side effect of sending output to the screen when run, that effect is invisible to the formal foundation. The ``print axioms`` command shows that the expressions ``hello_world`` and ``print_squares`` depend on constants that have been added to the axiomatic foundation to implement the io primitives.

.. code-block:: lean

   import system.io
   open io

   def hello_world : io unit :=
   put_str "hello world\n"

   -- BEGIN
   #print axioms hello_world
   -- END

Within the logical foundation, these constants are entirely opaque, objects about which that the axiomatic system has nothing to say. In this way, we can prove properties of programs involving ``io`` that do not depend in any way on the particular results of the input and output.
