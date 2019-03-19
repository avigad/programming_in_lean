.. _Monads:

Monads
======

In this chapter, we will describe a powerful abstraction known as a *monad*. A monad is a type constructor ``m : Type → Type`` that comes equipped with two special operations, ``return`` and ``bind``. If ``α`` is any type, think of ``m α`` as being a "virtual ``α``," or, as some people describe it, "an ``α`` inside a box."

For a given monad ``m``, the function ``return`` has type ``Π {α : Type}, α → m α``. The idea is that for any element ``a : α``, ``return a`` produces the virtual version of ``a``, or puts ``a`` inside the box.

Once we are inside the box, we cannot get out; there is no general way of taking an element of ``m α`` and obtaining an element of ``α``. But the ``bind`` operation gives us a way of turning some operations on ``α`` into operations inside the monad. Specifically, for a given monad ``m``, the function ``bind`` has type ``Π {α β : Type}, m α → (α → m β) → m β``. Suppose we have a function ``f`` that, given any element ``a : α``, produces a virtual element of ``β``; in more prosaic terms, ``f`` has type ``α → m β``. Suppose also that we have a virtual element of ``α``, that is, ``ma : m α``. If we could extract from ``ma`` a corresponding element ``a`` of ``α``, we could apply ``f`` to it to get a virtual element of ``β``. We cannot do that in general, but ``bind`` gives us a way of simulating the compound operation: it applies ``f`` directly "inside the box," and gives us an element of ``m β``.

As an example of how ``bind`` and ``return`` can be used, given any function ``f : α → β``, we can get a function ``map f : m α → m β`` by defining ``map f ma`` to be ``bind ma (λ a, return (f a)``. Roughly, given ``ma : m α``, the ``bind`` reaches into the box, finds an associated ``a``, and then puts ``f a`` back into the box.

For another example, given any element ``mma : m (m α)``, the expression ``monad.bind mma id`` has type ``m α``. This means that even though we cannot in general extract an element of ``β`` from ``m β``, we *can* do it when ``β`` itself is a virtual type, ``m α``. The expression ``monad.bind mma id`` reaches into the ``m (m α)`` box, catches hold of an element of ``m α``, and simply leaves it in the ``m α`` box.

If you have never come across the notion of a monad before, these operations will seem quite mysterious. But instances of ``return`` and ``bind`` arise in many natural ways, and the goal of this chapter is to show you some examples. Roughly, they arise in situations where ``m`` is a type construction with the property that functions in the ordinary realm of types can be transported, uniformly, into functions in the realm of ``m``-types. This should sound quite general, and so it is perhaps not that surprising that monads be instantiated in many different ways. The power of the abstraction is not only that it provides general functions and notation the can be used in all these various instantiations, but also that it provides a helpful way of thinking about what they all have in common.

Lean implements the following common notation. First, we have the infix notation

.. code-block:: text

   ma >>= f

for ``bind ma f``. Think of this as saying "take an element ``a`` out of the box, and send it to ``f``." Remember, we are allowed to do that as long as the return type of ``f`` is of the form ``m β``. We also have the infix notation,

.. code-block:: text

   ma >> mb

for ``bind ma (λ a, mb)``. This takes an element ``a`` out of the box, ignores it entirely, and then returns ``mb``. These two pieces of notation are most useful in situations where the act of taking an element of the box can be viewed as inducing a change of state. In situations like that, you can think of ``ma >>= f`` as saying "do ``ma``, take the result, and then send it to ``f``." You can then think of of ``ma >> mb`` more simply as "do ``ma``, then do ``mb``." In this way, monads provide a way of simulating features of imperative programming languages in a functional setting. But, we will see, they do a lot more than that.

Thinking of monads in terms of performing actions while computing results is quite powerful, and Lean provides notation to support that perspective. The expression

.. code-block:: text

   do a ← ma, t

is syntactic sugar for ``ma >>= (λ a, t)``. Here ``t`` is typically an expression that depends on ``a``, and it should have type ``m β`` for some ``β``. So you can read ``do a ← ma, t`` as reaching into the box, extracting an ``a``, and then continuing the computation with ``t``. Similarly, ``do s, t`` is syntactic sugar for ``s >> t``, supporting the reading "do ``s``, then do ``t``." The notation supports iteration, so, for example,

.. code-block:: text

   do a ← s,
      b ← t,
      f a b,
      return (g a b)

is syntactic sugar for

.. code-block:: text

   bind s (λ a, bind t (λ b, bind (f a b) (λ c, return (g a b)))).

It supports the reading "do ``s`` and extract ``a``, do ``t`` and extract ``b``, do ``f a b``, then return the value ``g a b``."

Incidentally, as you may have guessed, a monad is implemented as a type class in Lean. In other words, ``return`` really has type

.. code-block:: text

   Π {m : Type → Type} [monad m] {α : Type}, α → m α},

and ``bind`` really has type

.. code-block:: text

   Π {m : Type → Type} [monad m] {α β : Type}, m α → (α → m β) → m β.

In general, the relevant monad can be inferred from the expressions in which ``bind`` and ``return`` appear, and the monad structure is then inferred by type class inference.

There is a constraint, namely that when we use monads all the types we apply the monad to have to live in the same type universe. When all the types in question appear as parameters to a definition, Lean's elaborator will infer that constraint. When we declare variables below, we will satisfy that constraint by explicitly putting them in the same universe.

The option monad
----------------

The ``option`` constructor provides what is perhaps the simplest example of a monad. Recall that an element of ``option α`` is either of the form ``some a`` for some element ``a : α``, or ``none``. So an element ``a`` of ``option α`` is a "virtual ``α``" in the sense of being either an element of ``α`` or an empty promise.

The associated ``return`` is just ``some``: given an element ``a`` of ``α``, ``some a`` returns a virtual ``α``. It is also clear that we cannot go in the opposite direction: given an element ``ma : option α``, there is no way, in general, of producing an element of ``α``. But we can simulate extraction of such an element as long as we are willing to stay in the virtual land of ``options``, by defining ``bind`` as follows:

.. code-block:: lean

   namespace hidden

   -- BEGIN
   def bind {α β : Type} (oa : option α) (f : α → option β) :
     option β :=
   match oa with
   | (some a) := f a
   | none     := none
   end
   -- END

   end hidden

If the element ``oa`` is ``some a``, we can simply apply ``f`` to ``a``, and otherwise we simply return ``none``. Notice how the ``do`` notation allows us to chain these operations:

.. code-block:: lean

   universe u
   variables {α β γ δ : Type.{u}} (oa : option α)
   variables (f : α → option β) (g : α → β → option γ)
             (h : α → β → γ → option δ)

   example : option β :=
   do a ← oa,
      b ← f a,
      return b

   example : option δ :=
   do a ← oa,
      b ← f a,
      c ← g a b,
      h a b c

Think of ``f``, ``g``, and ``h`` as being partial functions on their respective domains, where a return value of ``none`` indicates that the function is undefined for the given input. Intuitively, the second example above returns ``h a (f a) (g a (f a))``, assuming ``oa`` is ``some a`` and all the subterms of that expression are defined. The expression ``h a (f a) (g a (f a))`` does not actually type check; for example, the second argument of ``h`` should be of type ``β`` rather than ``option β``. But monadic notation allows us to simulate the computation of a possibly undefined term, where the bind operation serves to percolate a value of ``none`` to the output.

The list monad
--------------

Our next example of a monad is the ``list`` monad. In the last section we thought of a function ``f : α → option β`` as a function which, on input ``α``, possibly returns an element of ``β``. Now we will think of a function ``f : α → list β`` as a function which, on input ``α``, returns a list of possible values for the output. This monad is sometimes also called the ``nondeterministic`` monad, since we can think of ``f`` as a computation which may nondeterministically return any of the elements in the list.

It is easy to insert a value ``a : α`` into ``list α``; we define ``return a`` to be just the singleton list ``[a]``. Now, given ``la : list α`` and ``f : α → list β``, how should we define the bind operation ``la >>= f``? Intuitively, ``la`` represents any of the possible values occurring in the list, and for each such element ``a``, ``f`` may return any of the elements in ``f a``. We can then gather all the possible values of the virtual application by applying ``f`` to each element of ``la`` and merging the results into a single list:

.. code-block:: lean

   open list
   namespace hidden

   -- BEGIN
   def bind {α β : Type} (la : list α) (f : α → list β) : list β :=
   join (map f la)
   -- END

   end hidden

Since the example in the previous section used nothing more than generic monad operations, we can replay it in the ``list`` setting:

.. code-block:: lean

   universe u
   variables {α β γ δ : Type.{u}} (la : list α)
   variables (f : α → list β) (g : α → β → list γ)
             (h : α → β → γ → list δ)

   example : list δ :=
   do a ← la,
      b ← f a,
      c ← g a b,
      h a b c

Now think of the computation as representing the list of all possible values of the expression ``h a (f a) (g a (f a))``, where the bind percolates all possible values of the subexpressions to the final output.

Notice that the final output of the expression is a list, to which we can then apply any of the usual functions that deal with lists:

.. code-block:: lean

   open list

   variables {α β γ δ : Type} (la : list α)
   variables (f : α → list β) (g : α → β → list γ) (h : α → β → γ → list δ)

   example : ℕ :=
   length
     (do a ← la,
         b ← f a,
         c ← g a b,
         h a b c)

We can also move ``length`` inside the ``do`` expression, but then the output lives in ``ℕ`` instead of a ``list``. As a result, we need to use ``return`` to put the result in a monad:

.. code-block:: lean

   open list

   variables {α β γ δ : Type} (la : list α)
   variables (f : α → list β) (g : α → β → list γ)
             (h : α → β → γ → list δ)

   example : list ℕ :=
   do a ← la,
      b ← f a,
      c ← g a b,
      return (length (h a b c))

The state monad
---------------

Let us indulge in science fiction for a moment, and suppose we wanted to extend Lean's programming language with three global registers, ``x``, ``y``, and ``z``, each of which stores a natural number. When evaluating an expression ``g (f a)`` with ``f : α → β`` and ``g : β → γ``, ``f`` would start the computation with the registers initialized to ``0``, but could read and write values during the course of its computation. When ``g`` began its computation on ``f a``, the registers would be set they way that ``g`` left them, and ``g`` could continue to read and write values. (To avoid questions as to how we would interpret the flow of control in terms like ``h (k₁ a) (k₂ a)``, let us suppose that we only care about composing unary functions.)

There is a straightforward way to implement this behavior in a functional programming language, namely, by making the state of the three registers an explicit argument. First, let us define a data structure to hold the three values, and define the initial settings:

.. code-block:: lean

   structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)

   def init_reg : registers := registers.mk 0 0 0

Now, instead of defining ``f : α → β`` that operates on the state of the registers implicitly, we would define a function ``f₀ : α × registers → β × registers`` that operates on it explicitly. The function ``f₀`` would take an input ``a : α``, paired with the state of the registers at the beginning of the computation. It could the do whatever it wanted to the state, and return an output ``b : β`` paired with the new state. Similarly, we would replace ``g`` by a function ``g₀ : β × registers → γ × registers``. The result of the composite computation would be given by ``(g₀ (f₀ (a, init_reg))).1``. In other words, we would pair the value ``a`` with the initial setting of the registers, apply ``f₀`` and then ``g₀``, and take the first component. If we wanted to lay our hands on the state of the registers at the end of the computation, we could do that by taking the second component.

The biggest problem with this approach is the annoying overhead. To write functions this way, we would have to pair and unpair arguments and construct the new state explicitly. A key virtue of the monad abstraction is that it manages boilerplate operations in situations just like these.

Indeed, the monadic solution is not far away. By currying the input, we could take the input of ``f₀`` equally well to be ``α → registers → β × registers``. Now think of ``f₀`` as being a function which takes an input in ``α`` and returns an element of ``registers → β × registers``. Moreover, think of this output as representing a computation which starts with a certain state, and returns a value of ``β`` and a new state. Lo and behold, *that* is the relevant monad.

To be precise: for any type ``α``, the monad ``m α`` we are after is ``registers → α × registers``. We will call this the state monad for ``registers``. With this notation, the function ``f₀`` described above has type ``α → m β``, the function ``g₀`` has type ``β → m γ``, and the composition of the two on input ``a`` is ``f a >>= g``. Notice that the result is an element of ``m γ``, which is to say, it is a computation which takes any state and returns a value of ``γ`` paired with a new state. With ``do`` notation, we would express this instead as ``do b ← f a, g b``. If we want to leave the monad and extract a value in ``γ``, we can apply this expression to the initial state ``init_reg``, and take the first element of the resulting pair.

The last thing to notice is that there is nothing special about ``registers`` here. The same trick would work for any data structure that we choose to represent the state of a computation at a given point in time. We could describe, for example, registers, a stack, a heap, or any combination of these. For every type ``S``, Lean's library defines the state monad ``state S`` to be the monad that maps any type ``α`` to the type ``S → α × S``. (In the Lean implementation, the data is stored in a single field of a structure.) The particular monad described above is then simply ``state registers``.

Let us consider the ``return`` and ``bind`` operations. Given any ``a : α``, ``return a`` is given by ``λ s, (a, s)``. This represents the computation which takes any state ``s``, leaves it unchanged, and inserts ``a`` as the return value. The value of ``bind`` is tricker. Given an ``sa : state S α`` and an ``f : α → state S β``, remember that ``bind sa f`` is supposed to "reach into the box," extract an element ``a`` from ``sa``, and apply ``f`` to it inside the monad. Now, the result of ``bind sa f`` is supposed to be an element of ``state S β``, which is really a function ``S → β × S``. In other words, ``bind sa f`` is supposed to encode a function which operates on any state to produce an element of ``β`` to a new state. Doing so is straightforward: given any state ``s``, ``sa s`` consists of a pair ``(a, s₀)``, and applying ``f`` to ``a`` and then ``s₀`` yields the required element of ``β × S``. Thus the def of ``bind sa f`` is as follows:

.. code-block:: text

   λ s, match (sa s) with (a, s₀) := b a s₀

The library also defines operations ``get`` and ``put`` as follows:

.. code-block:: lean

    namespace hidden

    def get {S : Type} : state S S :=
    ⟨λ s, (s, s)⟩

    def put {S : Type} : S → state S unit := λ s₀, ⟨λ s, ((), s₀)⟩

    end hidden

With the argument ``S`` implicit, ``get`` is simply the state computation that does not change the current state, but also returns it as a value. The value ``put s₀`` is the state computation which replaces any state ``s`` by ``s₀`` and returns ``unit``. Notice that it is convenient to use ``unit`` for the output type any operation that does not return a value, though it may change the state.

Returning to our example, we can implement the register state monad and more focused get and put operations as follows:

.. code-block:: lean

   structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)

   -- BEGIN
   def init_reg : registers :=
   registers.mk 0 0 0

   @[reducible] def reg_state := state registers

   def get_x : reg_state ℕ :=
   do s ← get, return (registers.x s)

   def get_y : reg_state ℕ :=
   do s ← get, return (registers.y s)

   def get_z : reg_state ℕ :=
   do s ← get, return (registers.z s)

   def put_x (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk n (registers.y s) (registers.z s))

   def put_y (n : ℕ) : reg_state unit :=
   do s ← get,
      put(registers.mk (registers.x s) n (registers.z s))

   def put_z (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk (registers.x s) (registers.y s) n)
   -- END

We can then write a little register program as follows:

.. code-block:: lean

   structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)

   def init_reg : registers :=
   registers.mk 0 0 0

   @[reducible] def reg_state := state registers

   def get_x : reg_state ℕ :=
   do s ← get, return (registers.x s)

   def get_y : reg_state ℕ :=
   do s ← get, return (registers.y s)

   def get_z : reg_state ℕ :=
   do s ← get, return (registers.z s)

   def put_x (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk n (registers.y s) (registers.z s))

   def put_y (n : ℕ) : reg_state unit :=
   do s ← get,
      put(registers.mk (registers.x s) n (registers.z s))

   def put_z (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk (registers.x s) (registers.y s) n)

   -- BEGIN
   open nat

   def foo : reg_state ℕ :=
   do put_x 5,
      put_y 7,
      x ← get_x,
      put_z (x + 3),
      y ← get_y,
      z ← get_z,
      put_y (y + z),
      y ← get_y,
      return (y + 2)
   -- END

To see the results of this program, we have to "run" it on the initial
state:

.. code-block:: lean

   structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)

   def init_reg : registers :=
   registers.mk 0 0 0

   @[reducible] def reg_state := state registers

   def get_x : reg_state ℕ :=
   do s ← get, return (registers.x s)

   def get_y : reg_state ℕ :=
   do s ← get, return (registers.y s)

   def get_z : reg_state ℕ :=
   do s ← get, return (registers.z s)

   def put_x (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk n (registers.y s) (registers.z s))

   def put_y (n : ℕ) : reg_state unit :=
   do s ← get,
      put(registers.mk (registers.x s) n (registers.z s))

   def put_z (n : ℕ) : reg_state unit :=
   do s ← get,
      put (registers.mk (registers.x s) (registers.y s) n)

   open nat

   def foo : reg_state ℕ :=
   do put_x 5,
      put_y 7,
      x ← get_x,
      put_z (x + 3),
      y ← get_y,
      z ← get_z,
      put_y (y + z),
      y ← get_y,
      return (y + 2)

   -- BEGIN
   #reduce foo.run init_reg
   -- END

The result is the pair ``(17, {x := 5, y := 15, z := 8})``, consisting
of the return value, ``y``, paired with the values of the three
registers.

The IO monad
------------

We can finally explain how Lean handles input and output: the constant ``io`` is axiomatically declared to be a monad with certain supporting operations. It is a kind of state monad, but in contrast to the ones discussed in the last section, here the state is entirely opaque to Lean. You can think of the state as "the real world," or, at least, the status of interaction with the user. Lean's axiomatically declared constants include the following:

.. code-block:: lean

   import system.io
   open io

   #check (@put_str : string → io unit)
   #check (@get_line : io string)

Here ``io.interface`` is a type class packing information needed to interpret the input output interface. Users can instantiate that type class in different ways, but they can also leave these variables uninstantiated in calls to Lean's virtual machine, which then substitutes the usual terminal io operations.

The expression ``put_str s`` changes the ``io`` state by writing ``s`` to output; the return type, ``unit``, indicates that no meaningful value is returned. The expression ``put_nat n`` does the analogous thing for a natural number, ``n``. The expression ``get_line``, in contrast; however you want to think of the change in ``io`` state, a ``string`` value is returned inside the monad. When we use the native virtual machine interpretation, thinking of the ``io`` monad as representing a state is somewhat heuristic, since within the Lean language, there is nothing that we can say about it. But when we run a Lean program, the interpreter does the right thing whenever it encounters the bind and return operations for the monad, as well as the constants above. In particular, in the example below, it ensures that the argument to ``put_nat`` is evaluated before the output is sent to the user, and that the expressions are printed in the right order.

.. code-block:: lean

   import system.io
   open io
   variable [io.interface]

   -- BEGIN
   #eval put_str "hello " >> put_str "world!" >> put_str (to_string (27 * 39))
   -- END

[TODO: somewhere – probably in a later chapter? – document the format
type and operations.]

Related type classes
--------------------

In addition to the monad type class, Lean defines all the following abstract type classes and notations.

.. code-block:: lean

   open monad
   namespace hidden
   -- BEGIN
   universe variables u v

   class functor (f : Type u → Type v) : Type (max (u+1) v) :=
   (map : Π {α β : Type u}, (α → β) → f α → f β)
   (map_const : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

   infixr ` <$> `:100 := functor.map
   infixr ` <$ `:100  := functor.map_const

   @[reducible] def functor.map_const_rev {f : Type u → Type v} [functor f] {α β : Type u} : f β → α → f α :=
   λ a b, b <$ a
   infixr ` $> `:100  := functor.map_const_rev

   class has_pure (f : Type u → Type v) :=
   (pure {} {α : Type u} : α → f α)

   export has_pure (pure)

   class has_seq (f : Type u → Type v) : Type (max (u+1) v) :=
   (seq  : Π {α β : Type u}, f (α → β) → f α → f β)

   infixl ` <*> `:60 := has_seq.seq

   class has_seq_left (f : Type u → Type v) : Type (max (u+1) v) :=
   (seq_left : Π {α β : Type u}, f α → f β → f α)

   infixl ` <* `:60  := has_seq_left.seq_left

   class has_seq_right (f : Type u → Type v) : Type (max (u+1) v) :=
   (seq_right : Π {α β : Type u}, f α → f β → f β)

   infixl ` *> `:60  := has_seq_right.seq_right

   class applicative (f : Type u → Type v) extends functor f, has_pure f, has_seq f, has_seq_left f, has_seq_right f :=
   (map       := λ _ _ x y, pure x <*> y)
   (seq_left  := λ α β a b, const β <$> a <*> b)
   (seq_right := λ α β a b, const α id <$> a <*> b)

   class has_orelse (f : Type u → Type v) : Type (max (u+1) v) :=
   (orelse  : Π {α : Type u}, f α → f α → f α)

   infixr ` <|> `:2 := has_orelse.orelse

   class alternative (f : Type u → Type v) extends applicative f, has_orelse f : Type (max (u+1) v) :=
   (failure : Π {α : Type u}, f α)

   section
   variables {f : Type u → Type v} [alternative f] {α : Type u}

   @[inline] def failure : f α :=
   alternative.failure f

   @[inline] def guard {f : Type → Type v} [alternative f] (p : Prop) [decidable p] : f unit :=
   if p then pure () else failure

   @[inline] def assert {f : Type → Type v} [alternative f] (p : Prop) [decidable p] : f (inhabited p) :=
   if h : p then pure ⟨h⟩ else failure

   /- Later we define a coercion from bool to Prop, but this version will still be useful.
      Given (t : tactic bool), we can write t >>= guardb -/
   @[inline] def guardb {f : Type → Type v} [alternative f] : bool → f unit
   | tt := pure ()
   | ff := failure

   @[inline] def optional (x : f α) : f (option α) :=
   some <$> x <|> pure none

   end
   -- END
   end hidden

The ``monad`` class extends both ``functor`` and ``applicative``, so both of these can be seen as even more abstract versions of ``monad``. On the other hand, not every ``monad`` is ``alternative``, and in the next chapter we will see an important example of one that is. One way to think about an alternative monad is to think of it as representing computations that can possibly fail, and, moreover, Intuitively, an alternative monad can be thought of supporting definitions that say "try ``a`` first, and if that doesn't work, try ``b``." A good example is the ``option`` monad, in which we can think of an element ``none`` as a computation that has failed. If ``a`` and ``b`` are elements of ``option α`` for some type ``α``, we can define ``a <|> b`` to have the value ``a`` if ``a`` is of the form ``some a₀``, and ``b`` otherwise.
