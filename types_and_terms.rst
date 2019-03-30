.. _Types_and_Terms:

Types and Terms
===============

Lean's foundational framework is a version of a logical system known as the *Calculus of Inductive Constructions*, or *CIC*. Programming in Lean amounts to writing down expressions in the system, and then evaluating them. You should keep in mind that, as a full-blown foundation for mathematics, the CIC is much more than a programming language. One can define all kinds of mathematical objects: number systems, ranging from the natural numbers to the complex numbers; algebraic structures, from semigroups to categories and modules over an arbitrary ring; limits, derivatives, and integrals, and other components of real and complex analysis; vector spaces and matrices; measure spaces; and much more. This provides an environment in which one can define data types alongside other mathematical objects, and write programs alongside mathematical proofs.

Terms in the Calculus of Inductive Constructions are therefore used to represent mathematical objects, programs, data types, assertions, and proofs. In the CIC, every term has a *type*, which indicates what sort of object it and how it behaves computationally. This chapter is a quick tour of some of the terms we can write in Lean. For a more detailed and exhaustive account, see `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`__.

Some Basic Types
----------------

In Lean:

-  ``#check`` can be used a check the type of an expression.
-  ``#print`` can be used to print information about an identifier, for example, the definition of a defined constant.
-  ``#reduce`` can be used to normalize a symbolic expression.
-  ``#eval`` can be used to run the bytecode-block evaluator on any closed term that has a computational interpretation.

Lean's standard library defines a number of data types, such as ``nat``, ``int``, ``list``, and ``bool``.

.. code-block:: lean

   #check nat
   #print nat

   #check int
   #print int

   #check list
   #print list

   #check bool
   #print bool

You can use the unicode-block symbols ``ℕ`` and ``ℤ`` for nat and int, respectively. The first can be entered with ``\N`` or ``\nat``, and the second can be entered with ``\Z`` or ``\int``.

The library includes standard operations on these types:

.. code-block:: lean

   #check 3 + 6 * 9
   #eval 3 + 6 * 9

   #check 1 :: 2 :: 3 :: [4, 5] ++ [6, 7, 8]
   #eval 1 :: 2 :: 3 :: [4, 5] ++ [6, 7, 8]

   #check tt && (ff || tt)
   #eval tt && (ff || tt)

By default, a numeral denotes a natural number. You can always specify an intended type ``t`` for an expression ``e`` by writing ``(e : t)``. In that case, Lean does its best to interpret the expression as an object of the given type, and raises an error if it does not succeed.

.. code-block:: lean

   #check (3 : ℤ)
   #check (3 : ℤ) + 6 * 9
   #check (3 + 6 * 9 : ℤ)

   #eval (3 + 6 * 9 : ℤ)

We can also declare variables ranging over elements and types.

.. code-block:: lean

   variables m n k : ℕ
   variables u v w : ℤ
   variable  α : Type
   variables l₁ l₂ : list ℕ
   variables s₁ s₂ : list α
   variable  a : α

   #check m + n * k
   #check u + v * w
   #check m :: l₁ ++ l₂
   #check s₁ ++ a :: s₂

The standard library adopts the convention of using the Greek letters ``α``, ``β``, and ``γ`` to range over types. You can type these with ``\a``, ``\b``, and ``\g``, respectively. You can type subscripts with ``\0``, ``\1``, ``\2``, and so on.

Lean will insert coercions automatically:

.. code-block:: lean

   variables m n k : ℕ
   variables u v w : ℤ

   -- BEGIN
   #check v + m
   -- END

The presence of a coercion is indicated by Lean's output, ``v + ↑m : ℤ``. Since Lean infers types sequentially as it processes an expression, you need to indicate the coercion manually if you write the arguments in the other order:

.. code-block:: lean

   variables m n k : ℕ
   variables u v w : ℤ

   -- BEGIN
   #check ↑m + v
   -- END

You can type the up arrow by writing ``\u``. This is notation for a generic coercion function, and Lean finds the appropriate one using type classes, as described below. The notations ``+``, ``*``, ``++`` similarly denote functions defined generically on any type that supports the relevant operations:

.. code-block:: lean

   #check @has_add.add
   #print has_add.add

   #check @has_mul.mul
   #print has_mul.mul

   #check @append
   #print append

Here, the ``@`` symbol before the name of the function indicates that Lean should display arguments that are usually left implicit. These are called, unsurprisingly, *implicit arguments*. In the examples above, type class resolution finds the relevant operations, which are declared in the relevant *namespaces*.

.. code-block:: lean

   #check nat.add
   #check nat.mul
   #check list.append
   #check list.cons

When generic functions and notations are available, however, it is usually better to use them, because Lean's automation is designed to work well with generic functions and facts. Incidentally, when infix notation is defined for a binary operation, Lean's parser will let you put the notation in parentheses to refer to the operation in prefix form:

.. code-block:: lean

   #check (+)
   #check (*)
   #check (≤)

Lean knows about Cartesian products and pairs:

.. code-block:: lean

   variables α β : Type
   variables (a₁ a₂ : α) (b : β) (n : ℕ)
   variables (p : α × β) (q : α × ℕ)

   #check α × β
   #check (a₁, a₂)
   #check (n, b)
   #check p.1
   #check p.2

   #reduce (n, b).1
   #reduce (2, 3).1
   #eval (2, 3).1

It interprets tuples as iterated products, associated to the right:

.. code-block:: lean

   variables α β : Type
   variables (a₁ a₂ : α) (b : β) (n : ℕ)

   #check (n, a₁, b)
   #reduce (n, a₁, b).2
   #reduce (n, a₁, b).2.2

Lean also knows about subtypes and option types, which are described in the next chapter.

Defining Functions
------------------

In Lean, one can define a new constant with the ``definition`` command, which can be abbreviated to ``def``.

.. code-block:: lean

   definition foo : ℕ := 3

   def bar : ℕ := 2 + 2

As with the ``#check`` command, Lean first attempts to elaborate the given expression, which is to say, fill in all the information that is left implicit. After that, it checks to make sure that the expression has the stated type. Assuming it succeeds, it creates a new constant with the given name and type, associates it to the expression after the ``:=``, and stores it in the environment.

The type of functions from ``α`` to ``β`` is denoted ``α → β``. We have already seen that a function ``f`` is applied to an element ``x`` in the domain type by writing ``f x``.

.. code-block:: lean

   variables α β : Type
   variables (a₁ a₂ : α) (b : β) (n : ℕ)
   variables f : ℕ → α
   variables g : α → β → ℕ

   #check f n
   #check g a₁
   #check g a₂ b
   #check f (g a₂ b)
   #check g (f (g a₂ b))

Conversely, functions are introduced using ``λ`` abstraction.

.. code-block:: lean

   variables (α : Type) (n : ℕ) (i : ℤ)

   #check λ x : ℕ, x + 3
   #check λ x, x + 3
   #check λ x, x + n
   #check λ x, x + i
   #check λ x y, x + y + 1
   #check λ x : α, x

As the examples make clear, you can leave out the type of the abstracted variable when it can be inferred. The following two definitions mean the same thing:

.. code-block:: lean

   def foo : ℕ → ℕ := λ x : ℕ, x + 3
   def bar := λ x, x + 3

Instead of using a lambda, you can abstract variables by putting them before the colon:

.. code-block:: lean

   def foo (x y : ℕ) : ℕ := x + y + 3
   def bar (x y) := x + y + 3

You can even test a definition without adding it to the environment, using the ``example`` command:

.. code-block:: lean

   example (x y) := x + y + 3

When variables have been declared, functions implicitly depend on the variables mentioned in the definition:

.. code-block:: lean

   variables (α : Type) (x : α)
   variables m n : ℕ

   def foo := x
   def bar := m + n + 3
   def baz (k) := m + k + 3

   #check foo
   #check bar
   #check baz

Evaluating expressions involving abstraction and application has the expected behavior:

.. code-block:: lean

   #reduce (λ x, x + 3) 2
   #eval (λ x, x + 3) 2

   def foo (x : ℕ) : ℕ := x + 3

   #reduce foo 2
   #eval foo 2

Both expressions evaluate to 5.

In the CIC, types are just certain kinds of objects, so functions can depend on types. For example, the following defines a polymorphic identity function:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   def id (α : Type) (x : α) : α := x

   #check id ℕ 3
   #eval id ℕ 3

   #check id
   -- END

   end hidden

Lean indicates that the type of ``id`` is ``Π α : Type, α → α``. This is an example of a *pi type*, also known as a dependent function type, since the type of the second argument to ``id`` depends on the first.

It is generally redundant to have to give the first argument to ``id`` explicitly, since it can be inferred from the second argument. Using curly braces marks the argument as *implicit*.

.. code-block:: lean

   namespace hidden

   -- BEGIN
   def id {α : Type} (x : α) : α := x

   #check id 3
   #eval id 3

   #check id
   -- END

   end hidden

In case an implicit argument follows the last given argument in a function application, Lean inserts the implicit argument eagerly and tries to infer it. Using double curly braces ``{{`` … ``}}``, or the unicode-block equivalents obtained with ``\{{`` and ``\}}``, tells the parser to be more conservative about inserting the argument. The difference is illustrated below.

.. code-block:: lean

   def id₁ {α : Type} (x : α) : α := x
   def id₂ ⦃α : Type⦄ (x : α) : α := x

   #check (id₁ : ℕ → ℕ)
   #check (id₂ : Π α : Type, α → α)

In the next section, we will see that Lean supports a hierarchy of type universes, so that the following definition of the identity function is more general:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   universe u
   def id {α : Type u} (x : α) := x
   -- END

   end hidden

If you ``#check @list.append``, you will see that, similarly, the append function takes two lists of elements of any type, where the type can occur in any type universe.

Incidentally, subsequent arguments to a dependent function can depend on arbitrary parameters, not just other types:

.. code-block:: lean

   variable vec : ℕ → Type
   variable foo : Π {n : ℕ}, vec n → vec n
   variable v : vec 3

   #check foo v

This is precisely the sense in which dependent type theory is dependent.

The CIC also supports recursive definitions on inductively defined types.

.. code-block:: lean

   open nat

   def exp (x : ℕ) : ℕ → ℕ
   | 0      := 1
   | (succ n) := exp n * (succ n)

We will provide lots of examples of those in the next chapter.

Defining New Types
------------------

In the version of the Calculus of Inductive Constructions implemented by Lean, we start with a sequence of type universes, ``Sort 0``, ``Sort 1``, ``Sort 2``, ``Sort 3``, … The universe ``Sort 0`` is called ``Prop`` and has special properties that we will describe later. ``Type u`` is a syntactic sugar for ``Sort (u+1)``. For each ``u``, an element ``t : Type u`` is itself a type. If you execute the following,

.. code-block:: lean

   universe u
   #check Type u

you will see that each ``Type u`` itself has type ``Type (u+1)``. The notation ``Type`` is shorthand for ``Type 0``, which is a shorthand for ``Sort 1``.

In addition to the type universes, the Calculus of Inductive Constructions provides two means of forming new types:

-  pi types
-  inductive types

Lean provides an additional means of forming new types:

-  quotient types

We discussed pi types in the last section. Quotient types provide a means of defining a new type given a type and an equivalence relation on that type. They are used in the standard library to define multisets, which are represented as lists that are considered the same when one is a permutation of another.

Inductive types are surprisingly useful. The natural numbers are defined inductively:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   inductive nat : Type
   | zero : nat
   | succ : nat → nat
   -- END

   end hidden

So is the type of lists of elements of a given type ``α``:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   universe u

   inductive list (α : Type u) : Type u
   | nil  : list
   | cons : α → list → list
   -- END

   end hidden

The booleans form an inductive type, as do, indeed, any finitely enumerated type:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   inductive bool : Type
   | tt : bool
   | ff : bool

   inductive Beatle : Type
   | John   : Beatle
   | Paul   : Beatle
   | George : Beatle
   | Ringo  : Beatle
   -- END
   end hidden

So are the type of binary trees, and the type of countably branching trees in which every node has children indexed by the type of natural numbers:

.. code-block:: lean

   inductive binary_tree : Type
   | empty : binary_tree
   | cons  : binary_tree → binary_tree → binary_tree

   inductive nat_tree : Type
   | empty : nat_tree
   | sup   : (ℕ → nat_tree) → nat_tree

What these examples all have in common is that the associated types are built up freely and inductively by the given *constructors*. For example, we can build some binary trees:

.. code-block:: lean

   inductive binary_tree : Type
   | empty : binary_tree
   | cons  : binary_tree → binary_tree → binary_tree

   -- BEGIN
   #check binary_tree.empty
   #check binary_tree.cons (binary_tree.empty) (binary_tree.empty)
   -- END

If we open the namespace ``binary_tree``, we can use shorter names:

.. code-block:: lean

   inductive binary_tree : Type
   | empty : binary_tree
   | cons  : binary_tree → binary_tree → binary_tree

   -- BEGIN
   open binary_tree

   #check cons empty (cons (cons empty empty) empty)
   -- END

In the Lean library, the identifier ``empty`` is used as a generic notation for things like the empty set, so opening the ``binary_tree`` namespaces means that the constant is overloaded. If you write ``#check empty``, Lean will complain about the overload; you need to say something like ``#check (empty : binary_tree)`` to disambiguate.

The ``inductive`` command axiomatically declares all of the following:

-  A constant, to denote the new type.
-  The associated constructors.
-  A corresponding *eliminator*.

The latter gives rise to the principles of recursion and induction that we will encounter in the next two chapters.

We will not give a precise specification of the inductive data types allowed by Lean, but only note here that the description is fairly small and straightforward, and can easily be given a set-theoretic interpretation. Lean also allows *mutual* inductive types and *nested* inductive types. As an example, in the definition below, the type under definition appears as a parameter to the ``list`` type:

.. code-block:: lean

   inductive tree (α : Type) : Type
   | node : α → list tree → tree

Such definitions are *not* among Lean's axoimatic primitives; rather, they are compiled down to more primitive constructions.

Records and Structures
----------------------

When computer scientists bundle data together, they tend to call the result a *record*. When mathematicians do the same, they call it a *structure*. Lean uses the keyword ``structure`` to introduce inductive definitions with a single constructor.

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

Here, ``mk`` is the constructor (if omitted, Lean assumes it is ``mk`` by default), and ``red``, ``green``, ``blue``, and ``name`` project the four values that are used to construct an element of ``color``.

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

   -- BEGIN
   def purple := color.mk 150 0 150 "purple"

   #eval color.red purple
   #eval color.green purple
   #eval color.blue purple
   #eval color.name purple
   -- END

Because records are so important, Lean provides useful notation for dealing with them. For example, when the type of the record can be inferred, Lean allows the use of *anonymous constructors* ``⟨`` … ``⟩``, entered as ``\<`` and ``\>``, or the ascii equivalents ``(|`` and ``|)``. Similarly, one can use the notation ``.1``, ``.2``, and so on for the projections.

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

   -- BEGIN
   def purple : color := ⟨150, 0, 150, "purple"⟩

   #eval purple.1
   #eval purple.2
   #eval purple.3
   #eval purple.4
   -- END

Alternatively, one can use the notation ``.`` to extract the relevant projections:

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

   def purple : color := ⟨150, 0, 150, "purple"⟩

   -- BEGIN
   #eval purple.red
   #eval purple.green
   #eval purple.blue
   #eval purple.name
   -- END

When the type of the record can be inferred, you can also use the following notation to build an instance, explicitly naming each component:

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

   -- BEGIN
   def purple : color :=
   { red := 150, blue := 0, green := 150, name := "purple" }
   -- END

You can also use the ``with`` keyword for *record update*, that is, to define an instance of a new record by modifying an existing one:

.. code-block:: lean

   structure color : Type :=
   mk :: (red : ℕ) (green : ℕ) (blue : ℕ) (name : string)

   def purple : color :=
   { red := 150, blue := 0, green := 150, name := "purple" }

   -- BEGIN
   def mauve := { purple with green := 100, name := "mauve" }

   #eval mauve.red
   #eval mauve.green
   -- END

Lean provides extensive support for reasoning generically about algebraic structures, in particular, allowing the inheritance and sharing of notation and facts. Chief among these is the use of *class inference*, in a manner similar to that used by functional programming languages like Haskell. For example, the Lean library declares the structures ``has_one`` and ``has_mul`` to support the generic notation ``1`` and ``*`` in structures which have a one and binary multiplication:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   universe u
   variables {α : Type u}

   class has_one (α : Type u) := (one : α)
   class has_mul (α : Type u) := (mul : α → α → α)
   -- END

   end hidden

The ``class`` command not only defines a structure (in the cases above, each storing only one piece of data), but also marks them as targets for *class inference*. The symbol ``*`` is notation for the identifier ``has_mul.mul``, and if you check the type of ``has_mul.mul``, you will see there is an implicit argument for an element of ``has_mul``:

.. code-block:: lean

   #check @has_mul.mul

The sole element of the ``has_mul`` structure is the relevant multiplication, which should be inferred from the type ``α`` of the arguments. Given an expression ``a * b`` where ``a`` and ``b`` have type ``α``, Lean searches through instances of ``has_mul`` that have been declared to the system, in search of one that matches the type ``α``. When it finds such an instance, it uses that as the argument to ``mul``.

With ``has_mul`` and ``has_one`` in place, some of the most basic objects of the algebraic hierarchy are defined as follows:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   universe u
   variables {α : Type u}

   class semigroup (α : Type u) extends has_mul α :=
   (mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

   class comm_semigroup (α : Type u) extends semigroup α :=
   (mul_comm : ∀ a b : α, a * b = b * a)

   class monoid (α : Type u) extends semigroup α, has_one α :=
   (one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a)
   -- END

   end hidden

There are a few things to note here. First, these definitions are introduced as ``class`` definitions also. This marks them as eligible for class inference, enabling Lean to find the ``semigroup``, ``comm_semigroup``, or ``monoid`` structure associated to a type, ``α``, when necessary. The ``extends`` keyword does two things: it defines the new structure by adding the given fields to those of the structures being extended, and it declares any instance of the new structure to be an instance of the previous ones. Finally, notice that the new elements of these structures are not data, but, rather, *properties* that the data is assumed to satisfy. It is a consequence of the encoding of propositions and proofs in dependent type theory that we can treat assumptions like associativity and commutativity in a manner similar to data. We will discuss this encoding in a later chapter.

Because any monoid is an instance of ``has_one`` and ``has_mul``, Lean can interpret ``1`` and ``*`` in any monoid.

.. code-block:: lean

   variables (M : Type) [monoid M]
   variables a b : M

   #check a * 1 * b

The declaration ``[monoid M]`` declares a variable ranging over the monoid structure, but leaves it anonymous. The variable is automatically inserted in any definition that depends on ``M``, and is marked for class inference. We can now define operations generically. For example, the notion of squaring an element makes sense in any structure with a multiplication.

.. code-block:: lean

   universe u
   def square {α : Type u} [has_mul α] (x : α) : α := x * x

Because ``monoid`` is an instance of ``has_mul``, we can then use the generic squaring operation in any monoid.

.. code-block:: lean

   universe u
   def square {α : Type u} [has_mul α] (x : α) : α := x * x

   -- BEGIN
   variables (M : Type) [monoid M]
   variables a b : M

   #check square a * square b
   -- END

.. _Mathematics_and_Computation:

Mathematics and Computation
---------------------------

Lean aims to support both mathematical abstraction alongside pragmatic computation, allowing both to interact in a common foundational framework. Some users will be interested in viewing Lean as a programming language, and making sure that every assertion has direct computational meaning. Others will be interested in treating Lean as a system for reasoning about abstract mathematical objects and assertions, which may not have straightforward computational interpretations. Lean is designed to be a comfortable environment for both kinds of users.

But Lean is also designed to support users who want to maintain both world views at once. This includes mathematical users who, having developed an abstract mathematical theory, would then like to start computing with the mathematical objects in a verified way. It also includes computer scientists and engineers who, having written a program or modeled a piece of hardware or software in Lean, would like to verify claims about it against a background mathematical theory of arithmetic, analysis, dynamical systems, or stochastic processes.

Lean employs a number of carefully chosen devices to support a clean and principled unification of the two worlds. Chief among these is the inclusion of a type ``Prop`` of propositions, or assertions. If ``p`` is an element of type ``Prop``, you can think of an element ``t : p`` as representing evidence that ``p`` is true, or a proof of ``p``, or simply the fact that ``p`` holds. The element ``t``, however, does not bear any computational information. In contrast, if ``α`` is an element of ``Type u`` for any ``u`` greater than 0 and ``t : α``, then ``t`` contains data, and can be evaluated.

Lean allows us to to define nonconstructive functions using familiar classical principles, provided we mark the associated definitions as ``noncomputable``.

.. code-block:: lean

   open classical
   local attribute [instance] prop_decidable

   noncomputable def choose (p : ℕ → Prop) : ℕ :=
   if h : (∃ n : ℕ, p n) then some h else 0

   noncomputable def inverse (f : ℕ → ℕ) (n : ℕ) : ℕ :=
   if h : (∃ m : ℕ, f m = n) then some h else 0

In this example, declaring the type class instance ``prop_decidable`` allows us to use a classical definition by cases, depending on whether an arbitrary proposition is true or false. Given an arbitrary predicate ``p`` on the natural numbers, ``choose p`` returns an ``n`` satisfying ``p n`` if there is one, and ``0`` otherwise. For example, ``p n`` may assert that ``n`` code-blocks a halting computation sequence for some Turing machine, on a given input. In that case, ``choose p`` magically decides whether or not such a computation exists, and returns one if it doesn't. The second definition makes a best effort to define an inverse to a function ``f`` from the natural numbers to the natural numbers, mapping each ``n`` to some ``m`` such that ``f m = n``, and zero otherwise.

Lean cannot (and does not even try) to generate bytecode for noncomputable functions. But expressions ``t : α``, where ``α`` is a type of data, can contain subexpressions that are elements of ``Prop``, and these can refer to nonconstructive objects. During the extraction of bytecode, these elements are simply ignored, and do not contribute to the computational content of ``t``.

For that reason, abstract elements in Lean's library can have *computational refinements*. For example, for every type, ``α``, there is another type, ``set α``, of sets of elements of ``α`` and some sets satisfy the property of being ``finite``. Saying that a set is finite is equivalent to saying that there exists a list that contains exactly the same elements. But this statement is a proposition, which means that it is impossible to extract such a list from the mere assertion that it exists. For that reason, the standard library also defines a type ``finset α``, which is better suited to computation. An element ``s : finset α`` is represented by a list of elements of ``α`` without duplicates. Using quotient types, we can arrange that lists that differ up to permutation are considered equal, and a defining principle of quotient types allows us to define a function on ``finset α`` in terms of any list that represents it, provided that we show that our definition is invariant under permutations of the list. Computationally, an element of ``finset α`` *is* just a list. Everything else is essentially a contract that we commit ourselves to obeying when working with elements of ``finset α``. The contract is important to reasoning about the results of our computations and their properties, but it plays no role in the computation itself.

As another example of the interaction between propositions and data, consider the fact that we do not always have algorithms that determine whether a proposition is true (consider, for example, the proposition that a Turing machine halts). In many cases, however, we do. For example, assertions ``m = n`` and ``m < n`` about natural numbers, and Boolean combinations of these, can be evaluated. Propositions like this are said to be *decidable*. Lean's library uses class inference to infer the decidability, and when it succeeds, you can use a decidable property in an ``if`` … ``then`` … ``else`` conditional statement. Computationally, what is going on is that class inference finds the relevant procedure, and the bytecode evaluator uses it.

One side effect of the choice of CIC as a foundation is that all functions we define, computational or not, are total. Once again, dependent type theory offers various mechanisms that we can use to restrict the range of applicability of a function, and some will be described later on.
