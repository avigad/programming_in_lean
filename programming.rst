.. _Programming_in_Lean:

Programming in Lean
===================

Lean aims to support both mathematical abstraction alongside pragmatic computation, allowing both to interact in a common foundational framework. Some users will be interested in viewing Lean as a programming language, and making sure that every assertion has direct computational meaning. Others will be interested in treating Lean as a system for reasoning about abstract mathematical objects and assertions, which may not have straightforward computational interpretations. Lean is designed to be a comfortable environment for both kinds of users.

But Lean is also designed to support users who want to maintain both world views at once. This includes mathematical users who, having developed an abstract mathematical theory, would then like to start computing with the mathematical objects in a verified way. It also includes computer scientists and engineers who, having written a program or modeled a piece of hardware or software in Lean, would like to verify claims about it against a background mathematical theory of arithmetic, analysis, dynamical systems, or stochastic processes.

Lean employs a number of carefully chosen devices to support a clean and principled unification of the two worlds. Chief among these is the inclusion of a type ``Prop`` of propositions, or assertions. If ``p`` is an element of type ``Prop``, you can think of an element ``t : p`` as representing evidence that ``p`` is true, or a proof of ``p``, or simply the fact that ``p`` holds. The element ``t``, however, does not bear any computational information. In contrast, if ``α`` is an element of ``Type u`` for any ``u`` greater than 0 and ``t : α``, then ``t`` contains data, and can be evaluated.

We saw in :numref:`Section %s <Nonconstructive_Definitions>` that Lean allows us to define functions that produce data from a proposition ``∃ x, p x``, but that such functions are marked as ``noncomputable``, and do not generate bytecode-block. Expressions ``t : α``, where ``α`` is a type of data, can contain subexpressions that are elements of ``Prop``, and these can even refer to nonconstructive objects. During the extraction of bytecode-block, these elements are simply ignored, and do not contribute to the computational content of ``t``.

For that reason, abstract elements in Lean's library can have *computational refinements*. For example, for every type, ``α``, there is another type, ``set α``, of sets of elements of ``α`` and some sets satisfy the property of being ``finite``. Saying that a set is finite is equivalent to saying that there exists a list that contains exactly the same elements. But this statement is a proposition, which means that it is impossible to extract such a list from the mere assertion that it exists. For that reason, the standard library also defines a type ``finset α``, which is better suited to computation. An element ``s : finset α`` is represented by a list of elements of ``α`` without duplicates. Using quotient types, we can arrange that lists that differ up to permutation are considered equal, and a defining principle of quotient types allows us to define a function on ``finset α`` in terms of any list that represents it, provided that we show that our definition is invariant under permutations of the list. Computationally, an element of ``finset α`` *is* just a list. Everything else is essentially a contract that we commit ourselves to obeying when working with elements of ``finset α``. The contract is important to reasoning about the results of our computations and their properties, but it plays no role in the computation itself.

As another example of the interaction between propositions and data, consider the fact that we do not always have algorithms that determine whether a proposition is true (consider, for example, the proposition that a Turing machine halts). In many cases, however, we do. For example, assertions ``m = n`` and ``m < n`` about natural numbers, and Boolean combinations of these, can be evaluated. Propositions like this are said to be *decidable*. Lean's library uses class inference to infer the decidability, and when it succeeds, you can use a decidable property in an ``if`` … ``then`` … ``else`` conditional statement. Computationally, what is going on is that class inference finds the relevant procedure, and the bytecode-block evaluator uses it.

One side effect of the choice of CIC as a foundation is that all functions we define, computational or not, are total. Once again, dependent type theory offers various mechanisms that we can use to restrict the range of applicability of a function, and some will be described below.

Evaluating Expressions
----------------------

When translating expressions to byte code-block, Lean's virtual machine evaluator ignores type information entirely. The whole elaborate typing schema of the CIC serves to ensure that terms make sense, and mean what we think they mean. Type checking is entirely static: when evaluating a term ``t`` of type ``α``, the bytecode-block evaluator ignores ``α``, and simply computes the value of ``t``, as described below. As noted above, any subexpressions of ``t`` whose type is an element of ``Prop`` are computationally irrelevant, and they are ignored too.

The evaluation of expressions follows the computational rules of the CIC. In particular:

-  To evaluate a function application ``(λ x, s) t``, the bytecode-block evaluator evaluates ``t``, and then evaluates ``s`` with ``x`` instantiated to ``t``.
-  To evaluate an eliminator for an inductively defined type — in other words, a function defined by pattern matching or recursion — the bytecode-block evaluator waits until all the arguments are given, evaluates the first one, and, on the basis of the result, applies the relevant case or recursive call.

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
   ((s.to_list).filter p).to_string

   def map (f : char → char) (l : string) : string :=
   (l.to_list.map f).to_string

   def to_lower (s : string) : string := s.map char.to_lower

   def reverse (s : string) : string := s.to_list.reverse.to_string

   def remove_punctuation (s : string) : string :=
   s.filter (λ c, ¬ char.is_punctuation c)

   end string

We can use these to write a procedure that tests to see whether a given sentence is a palindrome.

.. code-block:: lean

   namespace string

   def filter (p : char → Prop) [decidable_pred p] (s : string) : string :=
   ((s.to_list).filter p).to_string

   def map (f : char → char) (l : string) : string :=
   (l.to_list.map f).to_string

   def to_lower (s : string) : string := s.map char.to_lower

   def reverse (s : string) : string := s.to_list.reverse.to_string

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

   #eval fib 100

The naive implementation runs the risk of an exponential run time, since the computation of ``fib (n+2)`` calls for two independent computations of ``fib n``, one hidden in the computation of ``fib (n+1)``. In fact, the current Lean compilation scheme avoids this, because it joins the recursive falls in a single tuple and evaluates them both at once. We can do this explictly, thereby avoiding reliance on the inner workings of Lean's function definition system, by defining an auxiliary function that computes the values in pairs:

.. code-block:: lean

   def fib_aux : ℕ → ℕ × ℕ
   | 0     := (0, 1)
   | (n+1) := let p := fib_aux n in (p.2, p.1 + p.2)

   def fib n := (fib_aux n).2

   #eval fib 100

A similar solution is to use additional arguments to accumulate partial results:

.. code-block:: lean

   def fib_aux : ℕ → ℕ → ℕ → ℕ
   | 0     a b := b
   | (n+1) a b := fib_aux n b (a+b)

   def fib n := fib_aux n 0 1

   #eval fib 100

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

This contract ensures that ``first`` will never be called to evaluate the first element of an empty list. The check is entirely static; the evidence is ignored by the bytecode-block evaluator.

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
