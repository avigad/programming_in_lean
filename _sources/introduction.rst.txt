.. _Introduction:

Introduction
============

This tutorial can be viewed as a companion to `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`__, which presents Lean as a system for building mathematical libraries and stating and proving mathematical theorems. From that perspective, the point of Lean is to implement a formal axiomatic framework in which one can define mathematical objects and reason about them.

But expressions in Lean have a computational interpretation, which is to say, they can be *evaluated*. Any closed term of type ``nat`` – that is, any term of type ``nat`` without free variables – evaluates to a numeral, as long as it is defined in the computational fragment of Lean's foundational framework. Similarly, any closed term of type ``list nat`` evaluates to a list of numerals, and any closed term of type ``bool`` evaluates either to the boolean value ``tt``, for "true," or ``ff``, for "false."

This provides another perspective on Lean: instead of thinking of it as a theorem prover whose language just happens to have a computational interpretation, think of it as a programming language that just happens to come equipped with a rich specification language and an interactive environment for proving that programs meet their specifications. The specification language and proof system are quite powerful, rich enough, in fact, to include all conventional mathematics.

Lean's underlying logical framework, the Calculus of Inductive Constructions, constitutes a surprisingly good programming language. It is expressive enough to define all sorts of data structures, and it supports powerful abstractions. Programs written in the language can be evaluated efficiently by Lean's virtual-machine interpreter, and work is underway to support code extraction and efficient compilation in a future version of Lean.

Viewed from a computational perspective, the Calculus of Inductive Constructions is an instance of a purely functional programming language. This means that a program in Lean is simply an expression whose value is determined compositionally from the values of the other expressions it refers to, independent of any sort of ambient state of computation. There is no notion of storing a result in memory or changing the value of a global variable; computation is just evaluation of expressions. This paradigm makes it easier to reason about programs and verify their correctness. At the same time, we will see that Lean incorporates concepts and abstractions that make it feasible to use this paradigm in practice.

The underlying foundational framework imposes one restriction that is alien to most programming languages, namely, that every program is terminating. So, for example, every "while" loop has to be explicitly bounded, though, of course, we can consider the result of iterating an arbitrary computation ``n`` times for any given natural number ``n``. Lean provides flexible mechanisms for structural and well-founded recursion, allowing us to define functions in natural ways. At the same, the system provides complementary mechanisms for proving claims, using inductive principles that capture the structure of the function definitions.

One novel feature of Lean is that its programming language is also a *metaprogramming language*, which is to say, it can be used to extend the functionality of Lean itself. To that end, Lean allows us to mark metaprograms with the keyword `meta`. This does two things:

-  Metaprograms can use arbitrary recursive calls, with no concern for termination.
-  Metaprograms can access *metaconstants*, that is, primitive functions and objects that are implemented internally in Lean and are not meant to be trusted by the foundational framework.

To summarize, we can use Lean in any of the following ways:

-  as a programming language
-  as a system for verifying properties of programs
-  as a system for writing metaprograms, that is, programs that extend the functionality of Lean itself
