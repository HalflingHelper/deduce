Deduce is an automated proof checker meant for use in education. The
intended audience is students with (roughly) the following background
knowledge and skills:

* Basic programming skills in a mainstream language such as Java,
  Python, or C++, as one would learn in the introductory computer
  science course at a university.
* Some exposure to logic, as one would learn in a course on Discrete
  Mathematics (aka. Discrete Structures).

The primary goal of Deduce is to help students learn how to prove the
correctness of pure functional programs. The reason for the focus on
pure functional programs is because (1) those proofs are much more
straightforward to write than proofs of correctness of imperative
programs, so it serves as a better starting place educationally, and
(2) the technology for automatically checking those proofs is well
understood, so it's straightforward to build and maintain the Deduce
proof checker.

## Functional Programming in Deduce

Deduce supports the following language features:
* unions
* definitions
* recursive functions
* higher-order functions
* anonymous functions
* the natural numbers
* pairs
* booleans and conditional expressions
* switch

The following subsections describe each of these features.

### Unions

The `union` feature of Deduce is a tagged union.  A union declaration
provides the name for the union type.  The body of the union specifies
alternative ways to construct values of the union type. For example,
to represent a linked-list of natural numbers, we could define the
following union.

	union NatList {
	  empty;
	  node(Nat, NatList);
	}

We can then construct values of type `NatList` using the
alternatives. For example, `node(1, node(2, empty))` creates a
linked-list whose elements are the numbers `1` and `2`.

Unions may be recursive. An alternative within a union, such as `node`
above, may include a parameter whose type is again the same union
type, in this case `NatList`.

Deduce supports generic unions, that is, one can parameterize a union
with one or more type parameters. For example, we can generalize our
linked list to allow an arbitrary element type as follows.

	union List<T> {
	  empty;
	  node(T, List<T>);
	}

### Definitions

The `define` feature of Deduce associates a name with a value.  The
following two definitions associate the name `L23` with the
linked-list containing `2` and `3`, and the name `L13` with the
linked-list containing `1`, `2` and `3`.

	define L23 = node(2, node(3, empty))
	define L13 : List<Nat> = node(1, L23)

If desired, the type can be specified after the name, following a
colon.  In the above, `L13` is a list of natural numbers, so its type
is `List<Nat>`.


### Recursive Functions

The recursive functions of Deduce are somewhat special to make sure
they always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every
  alternative in the union.
* The first argument of every recursive call must be a sub-part of the
  current alternative of the union.

A recursive function begins with the `function` keyword, followed by
the name of the function, then the paramters types and the return
type. For example, here's the definition of a `length` function for
lists of natural numbers.

	function length(NatList) -> Nat {
	  length(empty) = 0;
	  length(node(n, next)) = 1 + length(next);
	}

There are two clauses in this definition, one for the `empty`
alternative and another for the `node` alternative.  One can think of
the clauses as pattern-matching on the union's alternatives.  In the
second clause, the pattern `node(n, next)` includes two pattern
variables `n` and `next` that bind the two sub-parts of the node.  The
expression after the `=` specifies the return value of the
function. The clause for `empty` says that its length is `0`.  The
clause for `node` says that its length is one more than the length of
the rest of the linked list.  Note that the recursive call
`length(next)` is allowed because `next` is a sub-part 
of `node(n,next)`.

Deduce supports generic functions, so we can generalize `length` to
work on lists with any element type as follows.

	function length<E>(List<E>) -> Nat {
	  length(empty) = 0;
	  length(node(n, next)) = 1 + length(next);
	}

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. For example, here
is the `append` function that combines two linked lists.

	function append<E>(List<E>, List<E>) -> List<E> {
	  append(empty, ys) = ys;
	  append(node(n, xs), ys) = node(n, append(xs, ys));
	}

### Higher-order Functions

Functions may be passed as parameters to a function and they may be
returned from a function. For example, the following function checks
whether every element of a list satisfies a predicate.

	function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
	  all_elements(empty, P) = true;
	  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P);
	}

### Anonymous Functions

Anonymous functions can be created with a `λ` expression.  For
example, the following computes whether all the elements of the list
`L13` are positive.

    define L13_positive = all_elements(L13, λx{ 0 < x })

### The Natural Numbers

The natural numbers are not a builtin type in Deduce but instead they
are defined as a `union` type:

	union Nat {
	  zero;
	  suc(Nat);
	}

The file `Nat.pf` includes the above definition together with many
operations on natural numbers and theorems about them.

### Pairs

Pairs are defined as a `union` type:

	union Pair<T,U> {
	  pair(T,U);
	}

The file `Pair.pf` includes the above definition and several
operations on pairs, such as `first` and `second`.

### Booleans and Conditional Expressions

Deduce includes the values `true` and `false` of type `bool` and the
usual boolean operations such as `and`, `or`, and `not`.  Deduce also
provides an if-then-else expression that branches on the value of a
boolean. For example, the following expression

    if 0 ≤ 1 then 3+4 else 5+6

is equivalent to `7`. 

### Switch

One can also `switch` on a value of union type.  For example, the
following `zip` function combines two lists into a list of pairs.  It
is a recursive function that pattern-matches on the first list and
uses `switch` to pattern-match on the second list.

	function zip<T,U>(List<T>, List<U>) -> List< Pair<T, U> > {
	  zip(empty, ys) = empty;
	  zip(node(x, xs'), ys) =
		switch ys {
		  case empty { empty }
		  case node(y, ys') { node(pair(x,y), zip(xs', ys')) }
		};
	}
